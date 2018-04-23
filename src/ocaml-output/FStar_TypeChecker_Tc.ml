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
        else (Prims.lift_native_int (0))  in
      let uu____48 = FStar_Options.reuse_hint_for ()  in
      match uu____48 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____53 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____53 l  in
          let uu___65_54 = env  in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid  in (lid, uu____80)  in
              FStar_Pervasives_Native.Some uu____75  in
            (tbl, uu____68)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___65_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___65_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___65_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___65_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___65_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___65_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___65_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___65_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___65_54.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___65_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___65_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___65_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___65_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___65_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___65_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___65_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___65_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___65_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___65_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___65_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___65_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___65_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___65_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___65_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___65_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___65_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___65_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___65_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___65_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___65_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___65_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___65_54.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___65_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___65_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___65_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___65_54.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____97 = FStar_TypeChecker_Env.current_module env  in
                let uu____98 =
                  let uu____99 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____99 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____97 uu____98
            | l::uu____101 -> l  in
          let uu___66_104 = env  in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid  in (lid, uu____130)
                 in
              FStar_Pervasives_Native.Some uu____125  in
            (tbl, uu____118)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___66_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___66_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___66_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___66_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___66_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___66_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___66_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___66_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___66_104.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___66_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___66_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___66_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___66_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___66_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___66_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___66_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___66_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___66_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___66_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___66_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___66_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___66_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___66_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___66_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___66_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___66_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___66_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___66_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___66_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___66_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___66_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___66_104.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___66_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___66_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___66_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___66_104.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____149 =
         let uu____150 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____150  in
       Prims.op_Negation uu____149)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____166 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____166 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____193 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____193
         then
           let uu____194 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____194
         else ());
        (let uu____196 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____196 with
         | (t',uu____204,uu____205) ->
             ((let uu____207 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____207
               then
                 let uu____208 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____208
               else ());
              t'))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____225 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____225
  
let check_nogen :
  'Auu____234 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____234 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____257 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____257)
  
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
        let fail1 uu____292 =
          let uu____293 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____298 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____293 uu____298  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____338)::(wp,uu____340)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____355 -> fail1 ())
        | uu____356 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____367 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____367 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____397 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____397 t  in
          let open_univs_binders n_binders bs =
            let uu____411 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____411 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____419 =
            let uu____426 =
              open_univs_binders (Prims.lift_native_int (0))
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____427 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____426 uu____427  in
          (match uu____419 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____438 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____438 with
                | (effect_params,env1,uu____447) ->
                    let uu____448 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____448 with
                     | (signature,uu____454) ->
                         let ed1 =
                           let uu___67_456 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___67_456.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___67_456.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___67_456.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___67_456.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___67_456.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___67_456.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___67_456.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___67_456.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___67_456.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___67_456.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___67_456.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___67_456.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___67_456.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___67_456.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___67_456.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___67_456.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___67_456.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___67_456.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____472 ->
                               let op uu____496 =
                                 match uu____496 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____516 =
                                       let uu____517 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____526 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____517
                                         uu____526
                                        in
                                     (us, uu____516)
                                  in
                               let uu___68_535 = ed1  in
                               let uu____536 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____537 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____538 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____539 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____540 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____541 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____542 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____543 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____544 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____545 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____546 =
                                 let uu____547 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____547  in
                               let uu____558 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____559 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____560 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___69_568 = a  in
                                      let uu____569 =
                                        let uu____570 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____570
                                         in
                                      let uu____579 =
                                        let uu____580 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____580
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___69_568.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___69_568.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___69_568.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___69_568.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____569;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____579
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___68_535.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___68_535.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___68_535.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___68_535.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____536;
                                 FStar_Syntax_Syntax.bind_wp = uu____537;
                                 FStar_Syntax_Syntax.if_then_else = uu____538;
                                 FStar_Syntax_Syntax.ite_wp = uu____539;
                                 FStar_Syntax_Syntax.stronger = uu____540;
                                 FStar_Syntax_Syntax.close_wp = uu____541;
                                 FStar_Syntax_Syntax.assert_p = uu____542;
                                 FStar_Syntax_Syntax.assume_p = uu____543;
                                 FStar_Syntax_Syntax.null_wp = uu____544;
                                 FStar_Syntax_Syntax.trivial = uu____545;
                                 FStar_Syntax_Syntax.repr = uu____546;
                                 FStar_Syntax_Syntax.return_repr = uu____558;
                                 FStar_Syntax_Syntax.bind_repr = uu____559;
                                 FStar_Syntax_Syntax.actions = uu____560;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___68_535.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____623 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____628 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____623 uu____628  in
                           let uu____635 =
                             let uu____636 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____636.FStar_Syntax_Syntax.n  in
                           match uu____635 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____671)::(wp,uu____673)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____688 -> fail1 signature1)
                           | uu____689 -> fail1 signature1  in
                         let uu____690 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____690 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____714 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____721 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____721 with
                                     | (signature1,uu____733) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____734 ->
                                    let uu____737 =
                                      let uu____742 =
                                        let uu____743 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____743)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____742
                                       in
                                    (match uu____737 with
                                     | (uu____752,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____755 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____755
                                 in
                              ((let uu____757 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____757
                                then
                                  let uu____758 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____759 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____760 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____761 =
                                    let uu____762 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____762
                                     in
                                  let uu____763 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____758 uu____759 uu____760 uu____761
                                    uu____763
                                else ());
                               (let check_and_gen' env3 uu____785 k =
                                  match uu____785 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____799::uu____800 ->
                                           let uu____803 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____803 with
                                            | (us1,t1) ->
                                                let uu____812 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____812 with
                                                 | (us2,t2) ->
                                                     let uu____819 =
                                                       let uu____820 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____820 t2 k
                                                        in
                                                     let uu____821 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____821))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____826 =
                                      let uu____833 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____834 =
                                        let uu____837 =
                                          let uu____838 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____838
                                           in
                                        [uu____837]  in
                                      uu____833 :: uu____834  in
                                    let uu____839 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____826
                                      uu____839
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____843 = fresh_effect_signature ()
                                     in
                                  match uu____843 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____859 =
                                          let uu____866 =
                                            let uu____867 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____867
                                             in
                                          [uu____866]  in
                                        let uu____868 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____859
                                          uu____868
                                         in
                                      let expected_k =
                                        let uu____874 =
                                          let uu____881 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____882 =
                                            let uu____885 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____886 =
                                              let uu____889 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____890 =
                                                let uu____893 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____894 =
                                                  let uu____897 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____897]  in
                                                uu____893 :: uu____894  in
                                              uu____889 :: uu____890  in
                                            uu____885 :: uu____886  in
                                          uu____881 :: uu____882  in
                                        let uu____898 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____874
                                          uu____898
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____903 =
                                      let uu____906 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____906
                                       in
                                    let uu____907 =
                                      let uu____908 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____908
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____903
                                      uu____907
                                     in
                                  let expected_k =
                                    let uu____920 =
                                      let uu____927 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____928 =
                                        let uu____931 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____932 =
                                          let uu____935 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____936 =
                                            let uu____939 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____939]  in
                                          uu____935 :: uu____936  in
                                        uu____931 :: uu____932  in
                                      uu____927 :: uu____928  in
                                    let uu____940 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____920
                                      uu____940
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____947 =
                                      let uu____954 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____955 =
                                        let uu____958 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____958]  in
                                      uu____954 :: uu____955  in
                                    let uu____959 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____947
                                      uu____959
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____963 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____963 with
                                  | (t,uu____969) ->
                                      let expected_k =
                                        let uu____973 =
                                          let uu____980 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____981 =
                                            let uu____984 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____985 =
                                              let uu____988 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____988]  in
                                            uu____984 :: uu____985  in
                                          uu____980 :: uu____981  in
                                        let uu____989 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____973
                                          uu____989
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____994 =
                                      let uu____997 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____997
                                       in
                                    let uu____998 =
                                      let uu____999 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____999
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____994
                                      uu____998
                                     in
                                  let b_wp_a =
                                    let uu____1011 =
                                      let uu____1018 =
                                        let uu____1019 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1019
                                         in
                                      [uu____1018]  in
                                    let uu____1020 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1011
                                      uu____1020
                                     in
                                  let expected_k =
                                    let uu____1026 =
                                      let uu____1033 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1034 =
                                        let uu____1037 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1038 =
                                          let uu____1041 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1041]  in
                                        uu____1037 :: uu____1038  in
                                      uu____1033 :: uu____1034  in
                                    let uu____1042 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1026
                                      uu____1042
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1049 =
                                      let uu____1056 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1057 =
                                        let uu____1060 =
                                          let uu____1061 =
                                            let uu____1062 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1062
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1061
                                           in
                                        let uu____1071 =
                                          let uu____1074 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1074]  in
                                        uu____1060 :: uu____1071  in
                                      uu____1056 :: uu____1057  in
                                    let uu____1075 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1049
                                      uu____1075
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1082 =
                                      let uu____1089 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1090 =
                                        let uu____1093 =
                                          let uu____1094 =
                                            let uu____1095 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1095
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1094
                                           in
                                        let uu____1104 =
                                          let uu____1107 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1107]  in
                                        uu____1093 :: uu____1104  in
                                      uu____1089 :: uu____1090  in
                                    let uu____1108 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1082
                                      uu____1108
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1115 =
                                      let uu____1122 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1122]  in
                                    let uu____1123 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1115
                                      uu____1123
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1127 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1127 with
                                  | (t,uu____1133) ->
                                      let expected_k =
                                        let uu____1137 =
                                          let uu____1144 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1145 =
                                            let uu____1148 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1148]  in
                                          uu____1144 :: uu____1145  in
                                        let uu____1149 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1137
                                          uu____1149
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1152 =
                                  let uu____1163 =
                                    let uu____1164 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1164.FStar_Syntax_Syntax.n  in
                                  match uu____1163 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1179 ->
                                      let repr =
                                        let uu____1181 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1181 with
                                        | (t,uu____1187) ->
                                            let expected_k =
                                              let uu____1191 =
                                                let uu____1198 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1199 =
                                                  let uu____1202 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1202]  in
                                                uu____1198 :: uu____1199  in
                                              let uu____1203 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1191 uu____1203
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
                                        let uu____1220 =
                                          let uu____1227 =
                                            let uu____1228 =
                                              let uu____1243 =
                                                let uu____1246 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1247 =
                                                  let uu____1250 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1250]  in
                                                uu____1246 :: uu____1247  in
                                              (repr1, uu____1243)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1228
                                             in
                                          FStar_Syntax_Syntax.mk uu____1227
                                           in
                                        uu____1220
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1269 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1269 wp  in
                                      let destruct_repr t =
                                        let uu____1284 =
                                          let uu____1285 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1285.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1284 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1296,(t1,uu____1298)::
                                             (wp,uu____1300)::[])
                                            -> (t1, wp)
                                        | uu____1343 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1354 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1354
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1355 =
                                          fresh_effect_signature ()  in
                                        match uu____1355 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1371 =
                                                let uu____1378 =
                                                  let uu____1379 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1379
                                                   in
                                                [uu____1378]  in
                                              let uu____1380 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1371 uu____1380
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
                                              let uu____1386 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1386
                                               in
                                            let wp_g_x =
                                              let uu____1390 =
                                                let uu____1395 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1396 =
                                                  let uu____1397 =
                                                    let uu____1398 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1398
                                                     in
                                                  [uu____1397]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1395 uu____1396
                                                 in
                                              uu____1390
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1407 =
                                                  let uu____1412 =
                                                    let uu____1413 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1413
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1422 =
                                                    let uu____1423 =
                                                      let uu____1426 =
                                                        let uu____1429 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1430 =
                                                          let uu____1433 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1434 =
                                                            let uu____1437 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1438 =
                                                              let uu____1441
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1441]
                                                               in
                                                            uu____1437 ::
                                                              uu____1438
                                                             in
                                                          uu____1433 ::
                                                            uu____1434
                                                           in
                                                        uu____1429 ::
                                                          uu____1430
                                                         in
                                                      r :: uu____1426  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1423
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1412 uu____1422
                                                   in
                                                uu____1407
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____1447 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____1447
                                              then
                                                let uu____1450 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____1451 =
                                                  let uu____1454 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____1454]  in
                                                uu____1450 :: uu____1451
                                              else []  in
                                            let expected_k =
                                              let uu____1459 =
                                                let uu____1466 =
                                                  let uu____1469 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____1470 =
                                                    let uu____1473 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____1473]  in
                                                  uu____1469 :: uu____1470
                                                   in
                                                let uu____1474 =
                                                  let uu____1477 =
                                                    let uu____1480 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1481 =
                                                      let uu____1484 =
                                                        let uu____1485 =
                                                          let uu____1486 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1486
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1485
                                                         in
                                                      let uu____1487 =
                                                        let uu____1490 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1491 =
                                                          let uu____1494 =
                                                            let uu____1495 =
                                                              let uu____1496
                                                                =
                                                                let uu____1503
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1503]
                                                                 in
                                                              let uu____1504
                                                                =
                                                                let uu____1507
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1507
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1496
                                                                uu____1504
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1495
                                                             in
                                                          [uu____1494]  in
                                                        uu____1490 ::
                                                          uu____1491
                                                         in
                                                      uu____1484 ::
                                                        uu____1487
                                                       in
                                                    uu____1480 :: uu____1481
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____1477
                                                   in
                                                FStar_List.append uu____1466
                                                  uu____1474
                                                 in
                                              let uu____1508 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1459 uu____1508
                                               in
                                            let uu____1511 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____1511 with
                                             | (expected_k1,uu____1519,uu____1520)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___70_1525 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___70_1525.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1535 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1535
                                           in
                                        let res =
                                          let wp =
                                            let uu____1542 =
                                              let uu____1547 =
                                                let uu____1548 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1548
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1557 =
                                                let uu____1558 =
                                                  let uu____1561 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1562 =
                                                    let uu____1565 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1565]  in
                                                  uu____1561 :: uu____1562
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1558
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1547 uu____1557
                                               in
                                            uu____1542
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1571 =
                                            let uu____1578 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1579 =
                                              let uu____1582 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1582]  in
                                            uu____1578 :: uu____1579  in
                                          let uu____1583 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1571
                                            uu____1583
                                           in
                                        let uu____1586 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____1586 with
                                        | (expected_k1,uu____1600,uu____1601)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1605 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1605 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1626 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____1645 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____1655 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____1655 with
                                               | (usubst,uvs) ->
                                                   let uu____1678 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____1679 =
                                                     let uu___71_1680 = act
                                                        in
                                                     let uu____1681 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____1682 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____1683 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___71_1680.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___71_1680.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____1681;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____1682;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____1683
                                                     }  in
                                                   (uu____1678, uu____1679))
                                             in
                                          match uu____1645 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____1689 =
                                                  let uu____1690 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____1690.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____1689 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____1714 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____1714
                                                    then
                                                      let uu____1717 =
                                                        let uu____1720 =
                                                          let uu____1721 =
                                                            let uu____1722 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____1722
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____1721
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____1720
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____1717
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____1738 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____1739 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____1739 with
                                               | (act_typ1,uu____1747,g_t) ->
                                                   let env' =
                                                     let uu___72_1750 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___72_1750.FStar_TypeChecker_Env.dep_graph)
                                                     }  in
                                                   ((let uu____1752 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____1752
                                                     then
                                                       let uu____1753 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____1754 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____1755 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____1753
                                                         uu____1754
                                                         uu____1755
                                                     else ());
                                                    (let uu____1757 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____1757 with
                                                     | (act_defn,uu____1765,g_a)
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
                                                         let uu____1769 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____1797
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____1797
                                                                with
                                                                | (bs1,uu____1807)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____1814
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1814
                                                                     in
                                                                    let uu____1817
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____1817
                                                                    with
                                                                    | 
                                                                    (k1,uu____1829,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____1831 ->
                                                               let uu____1832
                                                                 =
                                                                 let uu____1837
                                                                   =
                                                                   let uu____1838
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____1839
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____1838
                                                                    uu____1839
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____1837)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____1832
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____1769
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____1848
                                                                  =
                                                                  let uu____1849
                                                                    =
                                                                    let uu____1850
                                                                    =
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_k
                                                                    uu____1850
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g_a
                                                                    uu____1849
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____1848);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____1854
                                                                    =
                                                                    let uu____1855
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____1855.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____1854
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____1878
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____1878
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____1887
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1887
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1909
                                                                    =
                                                                    let uu____1910
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____1910]
                                                                     in
                                                                    let uu____1911
                                                                    =
                                                                    let uu____1920
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1920]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1909;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1911;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1921
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1921))
                                                                  | uu____1924
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____1927
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
                                                                    let uu____1929
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____1929))
                                                                   in
                                                                match uu____1927
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
                                                                    let uu___73_1938
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_1938.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_1938.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___73_1938.FStar_Syntax_Syntax.action_params);
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
                                match uu____1152 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1962 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1962
                                       in
                                    let uu____1965 =
                                      let uu____1972 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1972 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1993 ->
                                               let uu____1996 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____2002 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____2002 =
                                                             (Prims.lift_native_int (0)))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____1996
                                               then (gen_univs, t)
                                               else
                                                 (let uu____2012 =
                                                    let uu____2017 =
                                                      let uu____2018 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____2019 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____2018 uu____2019
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____2017)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____2012
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1965 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____2033 =
                                             let uu____2038 =
                                               let uu____2039 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____2039.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____2038)  in
                                           match uu____2033 with
                                           | ([],uu____2042) -> t
                                           | (uu____2053,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____2054,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____2072 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____2089 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____2089
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____2094 =
                                              ((n1 >=
                                                  (Prims.lift_native_int (0)))
                                                 &&
                                                 (let uu____2096 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____2096))
                                                && (m <> n1)
                                               in
                                            if uu____2094
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____2112 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2119 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2120 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2112 uu____2119
                                                  uu____2120
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2130 =
                                             close1
                                               (~-
                                                  (Prims.lift_native_int (1)))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2130 with
                                           | (univs2,defn) ->
                                               let uu____2137 =
                                                 close1
                                                   (~-
                                                      (Prims.lift_native_int (1)))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2137 with
                                                | (univs',typ) ->
                                                    let uu___74_2145 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___74_2145.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___74_2145.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___74_2145.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___75_2148 = ed2  in
                                           let uu____2149 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               return_wp
                                              in
                                           let uu____2150 =
                                             close1
                                               (Prims.lift_native_int (1))
                                               bind_wp
                                              in
                                           let uu____2151 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               if_then_else1
                                              in
                                           let uu____2152 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               ite_wp
                                              in
                                           let uu____2153 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               stronger
                                              in
                                           let uu____2154 =
                                             close1
                                               (Prims.lift_native_int (1))
                                               close_wp
                                              in
                                           let uu____2155 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               assert_p
                                              in
                                           let uu____2156 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               assume_p
                                              in
                                           let uu____2157 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               null_wp
                                              in
                                           let uu____2158 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               trivial_wp
                                              in
                                           let uu____2159 =
                                             let uu____2160 =
                                               close1
                                                 (Prims.lift_native_int (0))
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2160
                                              in
                                           let uu____2171 =
                                             close1
                                               (Prims.lift_native_int (0))
                                               return_repr
                                              in
                                           let uu____2172 =
                                             close1
                                               (Prims.lift_native_int (1))
                                               bind_repr
                                              in
                                           let uu____2173 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___75_2148.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___75_2148.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2149;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2150;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2151;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2152;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2153;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2154;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2155;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2156;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2157;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2158;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2159;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2171;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2172;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2173;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___75_2148.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____2177 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2177
                                           then
                                             let uu____2178 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2178
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
      let uu____2200 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2200 with
      | (effect_binders_un,signature_un) ->
          let uu____2217 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2217 with
           | (effect_binders,env1,uu____2236) ->
               let uu____2237 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2237 with
                | (signature,uu____2253) ->
                    let raise_error1 uu____2268 =
                      match uu____2268 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2294  ->
                           match uu____2294 with
                           | (bv,qual) ->
                               let uu____2305 =
                                 let uu___76_2306 = bv  in
                                 let uu____2307 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___76_2306.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___76_2306.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2307
                                 }  in
                               (uu____2305, qual)) effect_binders
                       in
                    let uu____2310 =
                      let uu____2317 =
                        let uu____2318 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2318.FStar_Syntax_Syntax.n  in
                      match uu____2317 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____2328)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____2350 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____2310 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2374 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2374
                           then
                             let uu____2375 =
                               let uu____2378 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2378  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2375
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2418 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2418 with
                           | (t2,comp,uu____2431) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2440 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2440 with
                          | (repr,_comp) ->
                              ((let uu____2462 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2462
                                then
                                  let uu____2463 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2463
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
                                let uu____2467 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____2469 =
                                    let uu____2470 =
                                      let uu____2471 =
                                        let uu____2486 =
                                          let uu____2493 =
                                            let uu____2498 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2499 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2498, uu____2499)  in
                                          [uu____2493]  in
                                        (wp_type, uu____2486)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2471
                                       in
                                    mk1 uu____2470  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2469
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2524 =
                                      let uu____2529 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2529)  in
                                    let uu____2530 =
                                      let uu____2537 =
                                        let uu____2538 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2538
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2537]  in
                                    uu____2524 :: uu____2530  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____2546 =
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
                                  let uu____2609 = item  in
                                  match uu____2609 with
                                  | (u_item,item1) ->
                                      let uu____2630 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2630 with
                                       | (item2,item_comp) ->
                                           ((let uu____2646 =
                                               let uu____2647 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2647
                                                in
                                             if uu____2646
                                             then
                                               let uu____2648 =
                                                 let uu____2653 =
                                                   let uu____2654 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2655 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2654 uu____2655
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2653)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2648
                                             else ());
                                            (let uu____2657 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2657 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____2675 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____2676 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____2677 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2677 with
                                | (dmff_env1,uu____2701,bind_wp,bind_elab) ->
                                    let uu____2704 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2704 with
                                     | (dmff_env2,uu____2728,return_wp,return_elab)
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
                                           let uu____2735 =
                                             let uu____2736 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2736.FStar_Syntax_Syntax.n
                                              in
                                           match uu____2735 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2780 =
                                                 let uu____2795 =
                                                   let uu____2800 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2800
                                                    in
                                                 match uu____2795 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2864 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____2780 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2903 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2903 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2920 =
                                                          let uu____2921 =
                                                            let uu____2936 =
                                                              let uu____2943
                                                                =
                                                                let uu____2948
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____2949
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2948,
                                                                  uu____2949)
                                                                 in
                                                              [uu____2943]
                                                               in
                                                            (wp_type,
                                                              uu____2936)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2921
                                                           in
                                                        mk1 uu____2920  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____2964 =
                                                      let uu____2973 =
                                                        let uu____2974 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2974
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2973
                                                       in
                                                    (match uu____2964 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____2995
                                                           =
                                                           let error_msg =
                                                             let uu____2997 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____2998 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2997
                                                               uu____2998
                                                              in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg)
                                                            in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____3003
                                                                   =
                                                                   let uu____3004
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____3004
                                                                    in
                                                                 if
                                                                   uu____3003
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____3006
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
                                                                   uu____3006
                                                                   (fun a239 
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort
                                                                in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2
                                                                in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type
                                                              in
                                                           let body3 =
                                                             let uu____3031 =
                                                               let uu____3036
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____3037
                                                                 =
                                                                 let uu____3038
                                                                   =
                                                                   let uu____3045
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____3045,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____3038]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____3036
                                                                 uu____3037
                                                                in
                                                             uu____3031
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____3070 =
                                                             let uu____3071 =
                                                               let uu____3078
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____3078]
                                                                in
                                                             b11 ::
                                                               uu____3071
                                                              in
                                                           let uu____3083 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____3070
                                                             uu____3083
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____3084 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____3086 =
                                             let uu____3087 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____3087.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3086 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____3131 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____3131
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____3144 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____3146 =
                                             let uu____3147 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____3147.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3146 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.lift_native_int (1)))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____3174 =
                                                 let uu____3175 =
                                                   let uu____3178 =
                                                     let uu____3179 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____3179
                                                      in
                                                   [uu____3178]  in
                                                 FStar_List.append uu____3175
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____3174 body what
                                           | uu____3180 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.lift_native_int (0))
                                           then t
                                           else
                                             (let uu____3200 =
                                                let uu____3201 =
                                                  let uu____3202 =
                                                    let uu____3217 =
                                                      let uu____3218 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3218
                                                       in
                                                    (t, uu____3217)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3202
                                                   in
                                                mk1 uu____3201  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3200)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3252 = f a2  in
                                               [uu____3252]
                                           | x::xs ->
                                               let uu____3257 =
                                                 apply_last1 f xs  in
                                               x :: uu____3257
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
                                           let uu____3279 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3279 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3309 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3309
                                                 then
                                                   let uu____3310 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3310
                                                 else ());
                                                (let uu____3312 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3312))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3321 =
                                                 let uu____3326 = mk_lid name
                                                    in
                                                 let uu____3327 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3326 uu____3327
                                                  in
                                               (match uu____3321 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3331 =
                                                        let uu____3334 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3334
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3331);
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
                                          (let uu____3439 =
                                             let uu____3442 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3443 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3442 :: uu____3443  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3439);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3549 =
                                               let uu____3552 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3553 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3552 :: uu____3553  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3549);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3656 =
                                                FStar_List.fold_left
                                                  (fun uu____3696  ->
                                                     fun action  ->
                                                       match uu____3696 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3717 =
                                                             let uu____3724 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3724
                                                               params_un
                                                              in
                                                           (match uu____3717
                                                            with
                                                            | (action_params,env',uu____3733)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3753
                                                                     ->
                                                                    match uu____3753
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3764
                                                                    =
                                                                    let uu___77_3765
                                                                    = bv  in
                                                                    let uu____3766
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___77_3765.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___77_3765.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3766
                                                                    }  in
                                                                    (uu____3764,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3770
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3770
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
                                                                    uu____3800
                                                                    ->
                                                                    let uu____3801
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3801
                                                                     in
                                                                    ((
                                                                    let uu____3805
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3805
                                                                    then
                                                                    let uu____3806
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3807
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3808
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3809
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3806
                                                                    uu____3807
                                                                    uu____3808
                                                                    uu____3809
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
                                                                    let uu____3813
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    let uu___78_3817
                                                                    = action
                                                                     in
                                                                    let uu____3818
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3819
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___78_3817.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___78_3817.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___78_3817.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3818;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3819
                                                                    }  in
                                                                    uu____3816
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3813))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3656 with
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
                                                      let uu____3852 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3853 =
                                                        let uu____3856 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3856]  in
                                                      uu____3852 ::
                                                        uu____3853
                                                       in
                                                    let uu____3857 =
                                                      let uu____3858 =
                                                        let uu____3859 =
                                                          let uu____3860 =
                                                            let uu____3875 =
                                                              let uu____3882
                                                                =
                                                                let uu____3887
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3888
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3887,
                                                                  uu____3888)
                                                                 in
                                                              [uu____3882]
                                                               in
                                                            (repr,
                                                              uu____3875)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3860
                                                           in
                                                        mk1 uu____3859  in
                                                      let uu____3903 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3858
                                                        uu____3903
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3857
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____3904 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____3906 =
                                                    let uu____3913 =
                                                      let uu____3914 =
                                                        let uu____3917 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3917
                                                         in
                                                      uu____3914.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____3913 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3927)
                                                        ->
                                                        let uu____3956 =
                                                          let uu____3973 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____3973
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____4031 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____3956
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____4081 =
                                                               let uu____4082
                                                                 =
                                                                 let uu____4085
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____4085
                                                                  in
                                                               uu____4082.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____4081
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____4110
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____4110
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____4123
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4148
                                                                     ->
                                                                    match uu____4148
                                                                    with
                                                                    | 
                                                                    (bv,uu____4154)
                                                                    ->
                                                                    let uu____4155
                                                                    =
                                                                    let uu____4156
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4156
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4155
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____4123
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
                                                                    let uu____4220
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4220
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4225
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4233
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4233
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4238
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4241
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4238,
                                                                    uu____4241)))
                                                              | uu____4248 ->
                                                                  let uu____4249
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4255
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4255
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4254)
                                                                     in
                                                                  raise_error1
                                                                    uu____4249))
                                                    | uu____4262 ->
                                                        let uu____4263 =
                                                          let uu____4268 =
                                                            let uu____4269 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____4269
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____4268)
                                                           in
                                                        raise_error1
                                                          uu____4263
                                                     in
                                                  (match uu____3906 with
                                                   | (pre,post) ->
                                                       ((let uu____4293 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4295 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4297 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___79_4299 =
                                                             ed  in
                                                           let uu____4300 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4301 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____4302 =
                                                             let uu____4303 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4303)
                                                              in
                                                           let uu____4310 =
                                                             let uu____4311 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4311)
                                                              in
                                                           let uu____4318 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____4319 =
                                                             let uu____4320 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4320)
                                                              in
                                                           let uu____4327 =
                                                             let uu____4328 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4328)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4300;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4301;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4302;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4310;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4318;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4319;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4327;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___79_4299.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____4335 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4335
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4353
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4353
                                                               then
                                                                 let uu____4354
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4354
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.lift_native_int (0))
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____4366
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    let uu____4378
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4378)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4369
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
                                                                    uu____4366;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4393
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4393
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4395
                                                                 =
                                                                 let uu____4398
                                                                   =
                                                                   let uu____4401
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4401
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4398
                                                                   sigelts'
                                                                  in
                                                               (uu____4395,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4467 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4467 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4502 = FStar_List.hd ses  in
            uu____4502.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4507 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4511,[],t,uu____4513,uu____4514);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4516;
               FStar_Syntax_Syntax.sigattrs = uu____4517;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4519,_t_top,_lex_t_top,_0_17,uu____4522);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4524;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4525;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4527,_t_cons,_lex_t_cons,_0_18,uu____4530);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4532;
                 FStar_Syntax_Syntax.sigattrs = uu____4533;_}::[]
               when
               ((_0_17 = (Prims.lift_native_int (0))) &&
                  (_0_18 = (Prims.lift_native_int (0))))
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
                 let uu____4592 =
                   let uu____4599 =
                     let uu____4600 =
                       let uu____4607 =
                         let uu____4608 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____4608
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4607, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4600  in
                   FStar_Syntax_Syntax.mk uu____4599  in
                 uu____4592 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.lift_native_int (0)), []));
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
                   let uu____4626 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4626
                    in
                 let hd1 =
                   let uu____4628 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4628
                    in
                 let tl1 =
                   let uu____4630 =
                     let uu____4631 =
                       let uu____4638 =
                         let uu____4639 =
                           let uu____4646 =
                             let uu____4647 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____4647
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4646, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4639  in
                       FStar_Syntax_Syntax.mk uu____4638  in
                     uu____4631 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4630
                    in
                 let res =
                   let uu____4656 =
                     let uu____4663 =
                       let uu____4664 =
                         let uu____4671 =
                           let uu____4672 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____4672
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4671,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4664  in
                     FStar_Syntax_Syntax.mk uu____4663  in
                   uu____4656 FStar_Pervasives_Native.None r2  in
                 let uu____4678 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4678
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
                          (Prims.lift_native_int (0)), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____4717 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4717;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4722 ->
               let err_msg =
                 let uu____4726 =
                   let uu____4727 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4727  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4726
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
        let uu____4748 = FStar_Syntax_Util.type_u ()  in
        match uu____4748 with
        | (k,uu____4754) ->
            let phi1 =
              let uu____4756 = tc_check_trivial_guard env1 phi k  in
              FStar_All.pipe_right uu____4756
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
          let uu____4797 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4797 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4828 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____4828 FStar_List.flatten  in
              ((let uu____4842 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____4844 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____4844)
                   in
                if uu____4842
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
                          let uu____4855 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4865,uu____4866,uu____4867,uu____4868,uu____4869)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4878 -> failwith "Impossible!"  in
                          match uu____4855 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4891 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4895,uu____4896,uu____4897,uu____4898,uu____4899)
                        -> lid
                    | uu____4908 -> failwith "Impossible"  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let res =
                  let uu____4921 =
                    (((FStar_List.length tcs) = (Prims.lift_native_int (0)))
                       ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4921
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
                (let uu____4943 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____4950 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____4950 en  in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun se  ->
    FStar_List.tryPick (FStar_ToSyntax_ToSyntax.get_fail_attr true)
      se.FStar_Syntax_Syntax.sigattrs
  
let list_of_option :
  'Auu____4971 .
    'Auu____4971 FStar_Pervasives_Native.option -> 'Auu____4971 Prims.list
  =
  fun uu___59_4980  ->
    match uu___59_4980 with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let (check_multi_contained :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option)
  =
  fun l1  ->
    fun l2  ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____5039 = collect1 tl1  in
            (match uu____5039 with
             | [] -> [(hd1, (Prims.lift_native_int (1)))]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + (Prims.lift_native_int (1)))) :: t
                 else (hd1, (Prims.lift_native_int (1))) :: (h, n1) :: t)
         in
      let summ l =
        let l3 = FStar_List.sortWith (fun x  -> fun y  -> x - y) l  in
        collect1 l3  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],uu____5196) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____5227,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.lift_native_int (0)))
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 > hd2 -> aux l12 tl2
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 < hd2 ->
            FStar_Pervasives_Native.Some
              (hd1, n1, (Prims.lift_native_int (0)))
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 = hd2 ->
            if n1 <> n2
            then FStar_Pervasives_Native.Some (hd1, n1, n2)
            else aux tl1 tl2
         in
      aux l11 l21
  
let rec (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____5439 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____5439
       then
         let uu____5440 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____5440
       else ());
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let uu____5443 = get_fail_se se  in
       match uu____5443 with
       | FStar_Pervasives_Native.Some errnos ->
           ((let uu____5462 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____5462
             then
               let uu____5463 =
                 let uu____5464 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____5464
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____5463
             else ());
            (let errs =
               FStar_Errors.catch_errors
                 (fun uu____5482  -> tc_decl' env1 se)
                in
             (let uu____5484 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____5484
              then
                (FStar_Util.print_string ">> Got issues:\n";
                 FStar_List.iter FStar_Errors.print_issue errs;
                 FStar_Util.print_string ">> //Got issues:\n")
              else ());
             (let uu____5488 =
                let uu____5503 =
                  let uu____5512 =
                    FStar_List.concatMap
                      (fun i  -> list_of_option i.FStar_Errors.issue_number)
                      errs
                     in
                  check_multi_contained errnos uu____5512  in
                (errs, uu____5503)  in
              match uu____5488 with
              | ([],uu____5535) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   FStar_Errors.raise_error
                     (FStar_Errors.Error_DidNotFail,
                       "This top-level definition was expected to fail, but it succeeded")
                     se.FStar_Syntax_Syntax.sigrng)
              | (uu____5563,FStar_Pervasives_Native.Some (e,n1,n2)) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   (let uu____5586 =
                      let uu____5591 =
                        let uu____5592 = FStar_Util.string_of_int e  in
                        let uu____5593 = FStar_Util.string_of_int n1  in
                        let uu____5594 = FStar_Util.string_of_int n2  in
                        FStar_Util.format3
                          "This top-level definition was expected to raise Error #%s %s times, but it raised it %s times"
                          uu____5592 uu____5593 uu____5594
                         in
                      (FStar_Errors.Error_DidNotFail, uu____5591)  in
                    FStar_Errors.raise_error uu____5586
                      se.FStar_Syntax_Syntax.sigrng))
              | (uu____5603,FStar_Pervasives_Native.None ) -> ([], []))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)

and (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let r = se.FStar_Syntax_Syntax.sigrng  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____5647 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____5672 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
          ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids
             in
          ([se1], [])
      | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let ses1 =
            let uu____5727 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1)
               in
            if uu____5727
            then
              let ses1 =
                let uu____5733 =
                  let uu____5734 =
                    let uu____5735 =
                      tc_inductive
                        (let uu___80_5744 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___80_5744.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___80_5744.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___80_5744.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___80_5744.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___80_5744.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___80_5744.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___80_5744.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___80_5744.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___80_5744.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___80_5744.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___80_5744.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___80_5744.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___80_5744.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___80_5744.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___80_5744.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___80_5744.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___80_5744.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___80_5744.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___80_5744.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___80_5744.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___80_5744.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___80_5744.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___80_5744.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___80_5744.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___80_5744.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___80_5744.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___80_5744.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___80_5744.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___80_5744.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___80_5744.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___80_5744.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___80_5744.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___80_5744.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___80_5744.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___80_5744.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___80_5744.FStar_TypeChecker_Env.dep_graph)
                         }) ses se.FStar_Syntax_Syntax.sigquals lids
                       in
                    FStar_All.pipe_right uu____5735
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____5734
                    (FStar_TypeChecker_Normalize.elim_uvars env1)
                   in
                FStar_All.pipe_right uu____5733
                  FStar_Syntax_Util.ses_of_sigbundle
                 in
              ((let uu____5756 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____5756
                then
                  let uu____5757 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___81_5760 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___81_5760.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___81_5760.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___81_5760.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___81_5760.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Inductive after phase 1: %s\n"
                    uu____5757
                else ());
               ses1)
            else ses  in
          let uu____5767 =
            tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
          (match uu____5767 with
           | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p r; ([se], []))
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
          let uu____5799 = cps_and_elaborate env ne  in
          (match uu____5799 with
           | (ses,ne1,lift_from_pure_opt) ->
               let effect_and_lift_ses =
                 match lift_from_pure_opt with
                 | FStar_Pervasives_Native.Some lift ->
                     [(let uu___82_5836 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___82_5836.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___82_5836.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___82_5836.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___82_5836.FStar_Syntax_Syntax.sigattrs)
                       });
                     lift]
                 | FStar_Pervasives_Native.None  ->
                     [(let uu___83_5838 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___83_5838.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___83_5838.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___83_5838.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___83_5838.FStar_Syntax_Syntax.sigattrs)
                       })]
                  in
               ([], (FStar_List.append ses effect_and_lift_ses)))
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let ne1 =
            let uu____5845 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env)
               in
            if uu____5845
            then
              let ne1 =
                let uu____5847 =
                  let uu____5848 =
                    let uu____5849 =
                      tc_eff_decl
                        (let uu___84_5852 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___84_5852.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___84_5852.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___84_5852.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___84_5852.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___84_5852.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___84_5852.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___84_5852.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___84_5852.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___84_5852.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___84_5852.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___84_5852.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___84_5852.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___84_5852.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___84_5852.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___84_5852.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___84_5852.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___84_5852.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___84_5852.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___84_5852.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___84_5852.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___84_5852.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___84_5852.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___84_5852.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___84_5852.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___84_5852.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___84_5852.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___84_5852.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___84_5852.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___84_5852.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___84_5852.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___84_5852.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___84_5852.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___84_5852.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___84_5852.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___84_5852.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___84_5852.FStar_TypeChecker_Env.dep_graph)
                         }) ne
                       in
                    FStar_All.pipe_right uu____5849
                      (fun ne1  ->
                         let uu___85_5856 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ne1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___85_5856.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___85_5856.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___85_5856.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___85_5856.FStar_Syntax_Syntax.sigattrs)
                         })
                     in
                  FStar_All.pipe_right uu____5848
                    (FStar_TypeChecker_Normalize.elim_uvars env)
                   in
                FStar_All.pipe_right uu____5847
                  FStar_Syntax_Util.eff_decl_of_new_effect
                 in
              ((let uu____5858 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____5858
                then
                  let uu____5859 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___86_5862 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___86_5862.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___86_5862.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___86_5862.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___86_5862.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Effect decl after phase 1: %s\n"
                    uu____5859
                else ());
               ne1)
            else ne  in
          let ne2 = tc_eff_decl env ne1  in
          let se1 =
            let uu___87_5867 = se  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_new_effect ne2);
              FStar_Syntax_Syntax.sigrng =
                (uu___87_5867.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals =
                (uu___87_5867.FStar_Syntax_Syntax.sigquals);
              FStar_Syntax_Syntax.sigmeta =
                (uu___87_5867.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___87_5867.FStar_Syntax_Syntax.sigattrs)
            }  in
          ([se1], [])
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let ed_src =
            FStar_TypeChecker_Env.get_effect_decl env
              sub1.FStar_Syntax_Syntax.source
             in
          let ed_tgt =
            FStar_TypeChecker_Env.get_effect_decl env
              sub1.FStar_Syntax_Syntax.target
             in
          let uu____5875 =
            let uu____5882 =
              FStar_TypeChecker_Env.lookup_effect_lid env
                sub1.FStar_Syntax_Syntax.source
               in
            monad_signature env sub1.FStar_Syntax_Syntax.source uu____5882
             in
          (match uu____5875 with
           | (a,wp_a_src) ->
               let uu____5897 =
                 let uu____5904 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____5904
                  in
               (match uu____5897 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____5920 =
                        let uu____5923 =
                          let uu____5924 =
                            let uu____5931 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____5931)  in
                          FStar_Syntax_Syntax.NT uu____5924  in
                        [uu____5923]  in
                      FStar_Syntax_Subst.subst uu____5920 wp_b_tgt  in
                    let expected_k =
                      let uu____5935 =
                        let uu____5942 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____5943 =
                          let uu____5946 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____5946]  in
                        uu____5942 :: uu____5943  in
                      let uu____5947 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____5935 uu____5947  in
                    let repr_type eff_name a1 wp =
                      let no_reify l =
                        let uu____5976 =
                          let uu____5981 =
                            FStar_Util.format1 "Effect %s cannot be reified"
                              l.FStar_Ident.str
                             in
                          (FStar_Errors.Fatal_EffectCannotBeReified,
                            uu____5981)
                           in
                        let uu____5982 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error uu____5976 uu____5982  in
                      let uu____5985 =
                        FStar_TypeChecker_Env.effect_decl_opt env eff_name
                         in
                      match uu____5985 with
                      | FStar_Pervasives_Native.None  -> no_reify eff_name
                      | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                          let repr =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [FStar_Syntax_Syntax.U_unknown] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr))
                             in
                          let uu____6017 =
                            let uu____6018 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            Prims.op_Negation uu____6018  in
                          if uu____6017
                          then no_reify eff_name
                          else
                            (let uu____6024 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____6025 =
                               let uu____6032 =
                                 let uu____6033 =
                                   let uu____6048 =
                                     let uu____6051 =
                                       FStar_Syntax_Syntax.as_arg a1  in
                                     let uu____6052 =
                                       let uu____6055 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____6055]  in
                                     uu____6051 :: uu____6052  in
                                   (repr, uu____6048)  in
                                 FStar_Syntax_Syntax.Tm_app uu____6033  in
                               FStar_Syntax_Syntax.mk uu____6032  in
                             uu____6025 FStar_Pervasives_Native.None
                               uu____6024)
                       in
                    let uu____6061 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____6113 =
                            if
                              (FStar_List.length uvs) >
                                (Prims.lift_native_int (0))
                            then
                              let uu____6122 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____6122 with
                              | (usubst,uvs1) ->
                                  let uu____6145 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____6146 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____6145, uu____6146)
                            else (env, lift_wp)  in
                          (match uu____6113 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if
                                   (FStar_List.length uvs) =
                                     (Prims.lift_native_int (0))
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____6159 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____6159))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____6186 =
                            if
                              (FStar_List.length what) >
                                (Prims.lift_native_int (0))
                            then
                              let uu____6199 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____6199 with
                              | (usubst,uvs) ->
                                  let uu____6224 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____6224)
                            else ([], lift)  in
                          (match uu____6186 with
                           | (uvs,lift1) ->
                               ((let uu____6243 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6243
                                 then
                                   let uu____6244 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____6244
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____6247 =
                                   let uu____6254 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____6254 lift1
                                    in
                                 match uu____6247 with
                                 | (lift2,comp,uu____6263) ->
                                     let uu____6264 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____6264 with
                                      | (uu____6277,lift_wp,lift_elab) ->
                                          let lift_wp1 =
                                            recheck_debug "lift-wp" env
                                              lift_wp
                                             in
                                          let lift_elab1 =
                                            recheck_debug "lift-elab" env
                                              lift_elab
                                             in
                                          if
                                            (FStar_List.length uvs) =
                                              (Prims.lift_native_int (0))
                                          then
                                            let uu____6288 =
                                              let uu____6291 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____6291
                                               in
                                            let uu____6292 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____6288, uu____6292)
                                          else
                                            (let uu____6296 =
                                               let uu____6305 =
                                                 let uu____6312 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____6312)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6305
                                                in
                                             let uu____6321 =
                                               let uu____6328 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____6328)  in
                                             (uu____6296, uu____6321))))))
                       in
                    (match uu____6061 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___88_6360 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___88_6360.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___88_6360.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___88_6360.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___88_6360.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___88_6360.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___88_6360.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___88_6360.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___88_6360.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___88_6360.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___88_6360.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___88_6360.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___88_6360.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___88_6360.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___88_6360.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___88_6360.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___88_6360.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___88_6360.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___88_6360.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___88_6360.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___88_6360.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___88_6360.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___88_6360.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___88_6360.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___88_6360.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___88_6360.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___88_6360.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___88_6360.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___88_6360.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___88_6360.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___88_6360.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___88_6360.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___88_6360.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___88_6360.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___88_6360.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___88_6360.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___88_6360.FStar_TypeChecker_Env.dep_graph)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____6378 =
                                 let uu____6383 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____6383 with
                                 | (usubst,uvs1) ->
                                     let uu____6406 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____6407 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____6406, uu____6407)
                                  in
                               (match uu____6378 with
                                | (env2,lift2) ->
                                    let uu____6412 =
                                      let uu____6419 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____6419
                                       in
                                    (match uu____6412 with
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
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp)
                                              in
                                           let lift_wp_a =
                                             let uu____6443 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____6444 =
                                               let uu____6451 =
                                                 let uu____6452 =
                                                   let uu____6467 =
                                                     let uu____6470 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____6471 =
                                                       let uu____6474 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____6474]  in
                                                     uu____6470 :: uu____6471
                                                      in
                                                   (lift_wp1, uu____6467)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6452
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6451
                                                in
                                             uu____6444
                                               FStar_Pervasives_Native.None
                                               uu____6443
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____6483 =
                                             let uu____6490 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____6491 =
                                               let uu____6494 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____6495 =
                                                 let uu____6498 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____6498]  in
                                               uu____6494 :: uu____6495  in
                                             uu____6490 :: uu____6491  in
                                           let uu____6499 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____6483
                                             uu____6499
                                            in
                                         let uu____6502 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____6502 with
                                          | (expected_k2,uu____6512,uu____6513)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    (Prims.lift_native_int (0))
                                                then
                                                  check_and_gen env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____6517 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____6517))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____6521 =
                             let uu____6522 =
                               let uu____6523 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____6523
                                 FStar_List.length
                                in
                             uu____6522 <> (Prims.lift_native_int (1))  in
                           if uu____6521
                           then
                             let uu____6536 =
                               let uu____6541 =
                                 let uu____6542 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____6543 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____6544 =
                                   let uu____6545 =
                                     let uu____6546 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____6546
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____6545
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____6542 uu____6543 uu____6544
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____6541)
                                in
                             FStar_Errors.raise_error uu____6536 r
                           else ());
                          (let uu____6561 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____6563 =
                                  let uu____6564 =
                                    let uu____6567 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____6567
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6564
                                    FStar_List.length
                                   in
                                uu____6563 <> (Prims.lift_native_int (1)))
                              in
                           if uu____6561
                           then
                             let uu____6580 =
                               let uu____6585 =
                                 let uu____6586 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____6587 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____6588 =
                                   let uu____6589 =
                                     let uu____6590 =
                                       let uu____6593 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____6593
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____6590
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____6589
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____6586 uu____6587 uu____6588
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____6585)
                                in
                             FStar_Errors.raise_error uu____6580 r
                           else ());
                          (let sub2 =
                             let uu___89_6608 = sub1  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___89_6608.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___89_6608.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp =
                                 (FStar_Pervasives_Native.Some lift_wp);
                               FStar_Syntax_Syntax.lift = lift1
                             }  in
                           let se1 =
                             let uu___90_6610 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___90_6610.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___90_6610.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___90_6610.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___90_6610.FStar_Syntax_Syntax.sigattrs)
                             }  in
                           ([se1], []))))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
          let env0 = env  in
          let uu____6625 =
            if (FStar_List.length uvs) = (Prims.lift_native_int (0))
            then (env, uvs, tps, c)
            else
              (let uu____6643 = FStar_Syntax_Subst.univ_var_opening uvs  in
               match uu____6643 with
               | (usubst,uvs1) ->
                   let tps1 = FStar_Syntax_Subst.subst_binders usubst tps  in
                   let c1 =
                     let uu____6672 =
                       FStar_Syntax_Subst.shift_subst
                         (FStar_List.length tps1) usubst
                        in
                     FStar_Syntax_Subst.subst_comp uu____6672 c  in
                   let uu____6679 =
                     FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                   (uu____6679, uvs1, tps1, c1))
             in
          (match uu____6625 with
           | (env1,uvs1,tps1,c1) ->
               let env2 = FStar_TypeChecker_Env.set_range env1 r  in
               let uu____6695 = FStar_Syntax_Subst.open_comp tps1 c1  in
               (match uu____6695 with
                | (tps2,c2) ->
                    let uu____6710 =
                      FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                    (match uu____6710 with
                     | (tps3,env3,us) ->
                         let uu____6728 =
                           FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                         (match uu____6728 with
                          | (c3,u,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env3
                                 g;
                               (let tps4 =
                                  FStar_Syntax_Subst.close_binders tps3  in
                                let c4 =
                                  FStar_Syntax_Subst.close_comp tps4 c3  in
                                let uu____6749 =
                                  let uu____6750 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_arrow
                                         (tps4, c4))
                                      FStar_Pervasives_Native.None r
                                     in
                                  FStar_TypeChecker_Util.generalize_universes
                                    env0 uu____6750
                                   in
                                match uu____6749 with
                                | (uvs2,t) ->
                                    let uu____6765 =
                                      let uu____6778 =
                                        let uu____6783 =
                                          let uu____6784 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____6784.FStar_Syntax_Syntax.n
                                           in
                                        (tps4, uu____6783)  in
                                      match uu____6778 with
                                      | ([],FStar_Syntax_Syntax.Tm_arrow
                                         (uu____6799,c5)) -> ([], c5)
                                      | (uu____6839,FStar_Syntax_Syntax.Tm_arrow
                                         (tps5,c5)) -> (tps5, c5)
                                      | uu____6866 ->
                                          failwith
                                            "Impossible (t is an arrow)"
                                       in
                                    (match uu____6765 with
                                     | (tps5,c5) ->
                                         (if
                                            (FStar_List.length uvs2) <>
                                              (Prims.lift_native_int (1))
                                          then
                                            (let uu____6910 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 uvs2 t
                                                in
                                             match uu____6910 with
                                             | (uu____6915,t1) ->
                                                 let uu____6917 =
                                                   let uu____6922 =
                                                     let uu____6923 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid
                                                        in
                                                     let uu____6924 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs2)
                                                         FStar_Util.string_of_int
                                                        in
                                                     let uu____6925 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t1
                                                        in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       uu____6923 uu____6924
                                                       uu____6925
                                                      in
                                                   (FStar_Errors.Fatal_TooManyUniverse,
                                                     uu____6922)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____6917 r)
                                          else ();
                                          (let se1 =
                                             let uu___91_6928 = se  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                    (lid, uvs2, tps5, c5,
                                                      flags1));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___91_6928.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___91_6928.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___91_6928.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___91_6928.FStar_Syntax_Syntax.sigattrs)
                                             }  in
                                           ([se1], []))))))))))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____6945,uu____6946,uu____6947) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_6951  ->
                  match uu___60_6951 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6952 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_let (uu____6957,uu____6958) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_6966  ->
                  match uu___60_6966 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6967 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          ((let uu____6977 = FStar_TypeChecker_Env.lid_exists env1 lid  in
            if uu____6977
            then
              let uu____6978 =
                let uu____6983 =
                  let uu____6984 = FStar_Ident.text_of_lid lid  in
                  FStar_Util.format1
                    "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                    uu____6984
                   in
                (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                  uu____6983)
                 in
              FStar_Errors.raise_error uu____6978 r
            else ());
           (let uu____6986 =
              if uvs = []
              then
                let uu____6987 =
                  let uu____6988 = FStar_Syntax_Util.type_u ()  in
                  FStar_Pervasives_Native.fst uu____6988  in
                check_and_gen env1 t uu____6987
              else
                (let uu____6994 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                 match uu____6994 with
                 | (uvs1,t1) ->
                     let env2 =
                       FStar_TypeChecker_Env.push_univ_vars env1 uvs1  in
                     let t2 =
                       let uu____7003 =
                         let uu____7004 = FStar_Syntax_Util.type_u ()  in
                         FStar_Pervasives_Native.fst uu____7004  in
                       tc_check_trivial_guard env2 t1 uu____7003  in
                     let t3 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.NoFullNorm;
                         FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                         env2 t2
                        in
                     let uu____7010 =
                       FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                     (uvs1, uu____7010))
               in
            match uu____6986 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___92_7026 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___92_7026.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___92_7026.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___92_7026.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___92_7026.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], [])))
      | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
          let uu____7036 = FStar_Syntax_Subst.open_univ_vars us phi  in
          (match uu____7036 with
           | (us1,phi1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
               let phi2 =
                 let uu____7053 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____7053
                 then
                   let phi2 =
                     let uu____7055 =
                       tc_assume
                         (let uu___93_7058 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___93_7058.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___93_7058.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___93_7058.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___93_7058.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___93_7058.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___93_7058.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___93_7058.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___93_7058.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___93_7058.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___93_7058.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___93_7058.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___93_7058.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___93_7058.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___93_7058.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___93_7058.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___93_7058.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___93_7058.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___93_7058.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___93_7058.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___93_7058.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___93_7058.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___93_7058.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___93_7058.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___93_7058.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___93_7058.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___93_7058.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___93_7058.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___93_7058.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___93_7058.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___93_7058.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___93_7058.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___93_7058.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___93_7058.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___93_7058.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___93_7058.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___93_7058.FStar_TypeChecker_Env.dep_graph)
                          }) phi1 r
                        in
                     FStar_All.pipe_right uu____7055
                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                          env1)
                      in
                   ((let uu____7060 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____7060
                     then
                       let uu____7061 =
                         FStar_Syntax_Print.term_to_string phi2  in
                       FStar_Util.print1 "Assume after phase 1: %s\n"
                         uu____7061
                     else ());
                    phi2)
                 else phi1  in
               let phi3 = tc_assume env1 phi2 r  in
               let uu____7065 =
                 if us1 = []
                 then FStar_TypeChecker_Util.generalize_universes env1 phi3
                 else
                   (let uu____7067 =
                      FStar_Syntax_Subst.close_univ_vars us1 phi3  in
                    (us1, uu____7067))
                  in
               (match uu____7065 with
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
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let env2 =
            FStar_TypeChecker_Env.set_expected_typ env1
              FStar_Syntax_Syntax.t_unit
             in
          let uu____7091 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
          (match uu____7091 with
           | (e1,c,g1) ->
               let uu____7109 =
                 let uu____7116 =
                   let uu____7119 =
                     FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                      in
                   FStar_Pervasives_Native.Some uu____7119  in
                 let uu____7120 =
                   let uu____7125 = FStar_Syntax_Syntax.lcomp_comp c  in
                   (e1, uu____7125)  in
                 FStar_TypeChecker_TcTerm.check_expected_effect env2
                   uu____7116 uu____7120
                  in
               (match uu____7109 with
                | (e2,uu____7135,g) ->
                    ((let uu____7138 = FStar_TypeChecker_Rel.conj_guard g1 g
                         in
                      FStar_TypeChecker_Rel.force_trivial_guard env2
                        uu____7138);
                     (let se1 =
                        let uu___94_7140 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_main e2);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___94_7140.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___94_7140.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___94_7140.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___94_7140.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      ([se1], [])))))
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          ((let uu____7152 = FStar_Options.debug_any ()  in
            if uu____7152
            then
              let uu____7153 =
                FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                 in
              let uu____7154 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.print2 "%s: Found splice of (%s)\n" uu____7153
                uu____7154
            else ());
           (let ses = env.FStar_TypeChecker_Env.splice env t  in
            let lids' =
              FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
            FStar_List.iter
              (fun lid  ->
                 let uu____7167 =
                   FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                 match uu____7167 with
                 | FStar_Pervasives_Native.Some uu____7170 -> ()
                 | FStar_Pervasives_Native.None  ->
                     let uu____7171 =
                       let uu____7176 =
                         let uu____7177 = FStar_Ident.string_of_lid lid  in
                         let uu____7178 =
                           let uu____7179 =
                             FStar_List.map FStar_Ident.string_of_lid lids'
                              in
                           FStar_All.pipe_left (FStar_String.concat ", ")
                             uu____7179
                            in
                         FStar_Util.format2
                           "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                           uu____7177 uu____7178
                          in
                       (FStar_Errors.Fatal_SplicedUndef, uu____7176)  in
                     FStar_Errors.raise_error uu____7171 r) lids;
            ([], ses)))
      | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let check_quals_eq l qopt q =
            match qopt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some q
            | FStar_Pervasives_Native.Some q' ->
                let uu____7240 =
                  ((FStar_List.length q) = (FStar_List.length q')) &&
                    (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                       q')
                   in
                if uu____7240
                then FStar_Pervasives_Native.Some q
                else
                  (let uu____7248 =
                     let uu____7253 =
                       let uu____7254 = FStar_Syntax_Print.lid_to_string l
                          in
                       let uu____7255 = FStar_Syntax_Print.quals_to_string q
                          in
                       let uu____7256 = FStar_Syntax_Print.quals_to_string q'
                          in
                       FStar_Util.format3
                         "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                         uu____7254 uu____7255 uu____7256
                        in
                     (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                       uu____7253)
                      in
                   FStar_Errors.raise_error uu____7248 r)
             in
          let rename_parameters lb =
            let rename_in_typ def typ =
              let typ1 = FStar_Syntax_Subst.compress typ  in
              let def_bs =
                let uu____7288 =
                  let uu____7289 = FStar_Syntax_Subst.compress def  in
                  uu____7289.FStar_Syntax_Syntax.n  in
                match uu____7288 with
                | FStar_Syntax_Syntax.Tm_abs (binders,uu____7299,uu____7300)
                    -> binders
                | uu____7321 -> []  in
              match typ1 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                    (val_bs,c);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars = uu____7331;_} ->
                  let has_auto_name bv =
                    FStar_Util.starts_with
                      (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      FStar_Ident.reserved_prefix
                     in
                  let rec rename_binders1 def_bs1 val_bs1 =
                    match (def_bs1, val_bs1) with
                    | ([],uu____7415) -> val_bs1
                    | (uu____7438,[]) -> val_bs1
                    | ((body_bv,uu____7462)::bt,(val_bv,aqual)::vt) ->
                        let uu____7499 = rename_binders1 bt vt  in
                        ((match ((has_auto_name body_bv),
                                  (has_auto_name val_bv))
                          with
                          | (true ,uu____7515) -> (val_bv, aqual)
                          | (false ,true ) ->
                              ((let uu___95_7517 = val_bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (let uu___96_7520 =
                                       val_bv.FStar_Syntax_Syntax.ppname  in
                                     {
                                       FStar_Ident.idText =
                                         ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                       FStar_Ident.idRange =
                                         (uu___96_7520.FStar_Ident.idRange)
                                     });
                                  FStar_Syntax_Syntax.index =
                                    (uu___95_7517.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort =
                                    (uu___95_7517.FStar_Syntax_Syntax.sort)
                                }), aqual)
                          | (false ,false ) -> (val_bv, aqual))) ::
                          uu____7499
                     in
                  let uu____7521 =
                    let uu____7528 =
                      let uu____7529 =
                        let uu____7542 = rename_binders1 def_bs val_bs  in
                        (uu____7542, c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____7529  in
                    FStar_Syntax_Syntax.mk uu____7528  in
                  uu____7521 FStar_Pervasives_Native.None r1
              | uu____7560 -> typ1  in
            let uu___97_7561 = lb  in
            let uu____7562 =
              rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                lb.FStar_Syntax_Syntax.lbtyp
               in
            {
              FStar_Syntax_Syntax.lbname =
                (uu___97_7561.FStar_Syntax_Syntax.lbname);
              FStar_Syntax_Syntax.lbunivs =
                (uu___97_7561.FStar_Syntax_Syntax.lbunivs);
              FStar_Syntax_Syntax.lbtyp = uu____7562;
              FStar_Syntax_Syntax.lbeff =
                (uu___97_7561.FStar_Syntax_Syntax.lbeff);
              FStar_Syntax_Syntax.lbdef =
                (uu___97_7561.FStar_Syntax_Syntax.lbdef);
              FStar_Syntax_Syntax.lbattrs =
                (uu___97_7561.FStar_Syntax_Syntax.lbattrs);
              FStar_Syntax_Syntax.lbpos =
                (uu___97_7561.FStar_Syntax_Syntax.lbpos)
            }  in
          let uu____7565 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.fold_left
                 (fun uu____7616  ->
                    fun lb  ->
                      match uu____7616 with
                      | (gen1,lbs1,quals_opt) ->
                          let lbname =
                            FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                             in
                          let uu____7658 =
                            let uu____7669 =
                              FStar_TypeChecker_Env.try_lookup_val_decl env1
                                (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            match uu____7669 with
                            | FStar_Pervasives_Native.None  ->
                                if lb.FStar_Syntax_Syntax.lbunivs <> []
                                then (false, lb, quals_opt)
                                else (gen1, lb, quals_opt)
                            | FStar_Pervasives_Native.Some ((uvs,tval),quals)
                                ->
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
                                  | uu____7754 ->
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
                                 (let uu____7797 =
                                    FStar_Syntax_Syntax.mk_lb
                                      ((FStar_Util.Inr lbname), uvs,
                                        FStar_Parser_Const.effect_ALL_lid,
                                        tval, def,
                                        (lb.FStar_Syntax_Syntax.lbpos))
                                     in
                                  (false, uu____7797, quals_opt1)))
                             in
                          (match uu____7658 with
                           | (gen2,lb1,quals_opt1) ->
                               (gen2, (lb1 :: lbs1), quals_opt1)))
                 (true, [],
                   (if se.FStar_Syntax_Syntax.sigquals = []
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (se.FStar_Syntax_Syntax.sigquals))))
             in
          (match uu____7565 with
           | (should_generalize,lbs',quals_opt) ->
               let quals =
                 match quals_opt with
                 | FStar_Pervasives_Native.None  ->
                     [FStar_Syntax_Syntax.Visible_default]
                 | FStar_Pervasives_Native.Some q ->
                     let uu____7891 =
                       FStar_All.pipe_right q
                         (FStar_Util.for_some
                            (fun uu___61_7895  ->
                               match uu___61_7895 with
                               | FStar_Syntax_Syntax.Irreducible  -> true
                               | FStar_Syntax_Syntax.Visible_default  -> true
                               | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                               | uu____7896 -> false))
                        in
                     if uu____7891
                     then q
                     else FStar_Syntax_Syntax.Visible_default :: q
                  in
               let lbs'1 = FStar_List.rev lbs'  in
               let e =
                 let uu____7906 =
                   let uu____7913 =
                     let uu____7914 =
                       let uu____7927 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_constant
                              FStar_Const.Const_unit)
                           FStar_Pervasives_Native.None r
                          in
                       (((FStar_Pervasives_Native.fst lbs), lbs'1),
                         uu____7927)
                        in
                     FStar_Syntax_Syntax.Tm_let uu____7914  in
                   FStar_Syntax_Syntax.mk uu____7913  in
                 uu____7906 FStar_Pervasives_Native.None r  in
               let env0 =
                 let uu___98_7946 = env1  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___98_7946.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___98_7946.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___98_7946.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___98_7946.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___98_7946.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___98_7946.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___98_7946.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___98_7946.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___98_7946.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___98_7946.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___98_7946.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize = should_generalize;
                   FStar_TypeChecker_Env.letrecs =
                     (uu___98_7946.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = true;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___98_7946.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___98_7946.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___98_7946.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___98_7946.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___98_7946.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___98_7946.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___98_7946.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___98_7946.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___98_7946.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___98_7946.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___98_7946.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___98_7946.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___98_7946.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___98_7946.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___98_7946.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___98_7946.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___98_7946.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___98_7946.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___98_7946.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___98_7946.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___98_7946.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___98_7946.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___98_7946.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let e1 =
                 let uu____7948 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env0)
                    in
                 if uu____7948
                 then
                   let drop_lbtyp e_lax =
                     let uu____7955 =
                       let uu____7956 = FStar_Syntax_Subst.compress e_lax  in
                       uu____7956.FStar_Syntax_Syntax.n  in
                     match uu____7955 with
                     | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                         let lb_unannotated =
                           let uu____7974 =
                             let uu____7975 = FStar_Syntax_Subst.compress e
                                in
                             uu____7975.FStar_Syntax_Syntax.n  in
                           match uu____7974 with
                           | FStar_Syntax_Syntax.Tm_let
                               ((uu____7978,lb1::[]),uu____7980) ->
                               let uu____7993 =
                                 let uu____7994 =
                                   FStar_Syntax_Subst.compress
                                     lb1.FStar_Syntax_Syntax.lbtyp
                                    in
                                 uu____7994.FStar_Syntax_Syntax.n  in
                               uu____7993 = FStar_Syntax_Syntax.Tm_unknown
                           | uu____7997 ->
                               failwith
                                 "Impossible: first phase lb and second phase lb differ in structure!"
                            in
                         if lb_unannotated
                         then
                           let uu___99_7998 = e_lax  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false,
                                     [(let uu___100_8010 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           FStar_Syntax_Syntax.tun;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbdef);
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___100_8010.FStar_Syntax_Syntax.lbpos)
                                       })]), e2));
                             FStar_Syntax_Syntax.pos =
                               (uu___99_7998.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___99_7998.FStar_Syntax_Syntax.vars)
                           }
                         else e_lax
                     | uu____8012 -> e_lax  in
                   let e1 =
                     let uu____8014 =
                       let uu____8015 =
                         let uu____8016 =
                           FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                             (let uu___101_8025 = env0  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___101_8025.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___101_8025.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___101_8025.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___101_8025.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___101_8025.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___101_8025.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___101_8025.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___101_8025.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___101_8025.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___101_8025.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___101_8025.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___101_8025.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___101_8025.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___101_8025.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___101_8025.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___101_8025.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___101_8025.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___101_8025.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___101_8025.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___101_8025.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___101_8025.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___101_8025.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___101_8025.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___101_8025.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___101_8025.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___101_8025.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___101_8025.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___101_8025.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___101_8025.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___101_8025.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___101_8025.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___101_8025.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___101_8025.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___101_8025.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___101_8025.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___101_8025.FStar_TypeChecker_Env.dep_graph)
                              }) e
                            in
                         FStar_All.pipe_right uu____8016
                           (fun uu____8036  ->
                              match uu____8036 with
                              | (e1,uu____8044,uu____8045) -> e1)
                          in
                       FStar_All.pipe_right uu____8015
                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                            env0)
                        in
                     FStar_All.pipe_right uu____8014 drop_lbtyp  in
                   ((let uu____8047 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____8047
                     then
                       let uu____8048 = FStar_Syntax_Print.term_to_string e1
                          in
                       FStar_Util.print1 "Let binding after phase 1: %s\n"
                         uu____8048
                     else ());
                    e1)
                 else e  in
               let uu____8051 =
                 let uu____8062 =
                   FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                    in
                 match uu____8062 with
                 | ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                        (lbs1,e2);
                      FStar_Syntax_Syntax.pos = uu____8081;
                      FStar_Syntax_Syntax.vars = uu____8082;_},uu____8083,g)
                     when FStar_TypeChecker_Rel.is_trivial g ->
                     let lbs2 =
                       let uu____8112 =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs1)
                           (FStar_List.map rename_parameters)
                          in
                       ((FStar_Pervasives_Native.fst lbs1), uu____8112)  in
                     let quals1 =
                       match e2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_meta
                           (uu____8130,FStar_Syntax_Syntax.Meta_desugared
                            (FStar_Syntax_Syntax.Masked_effect ))
                           -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                       | uu____8135 -> quals  in
                     ((let uu___102_8143 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___102_8143.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___102_8143.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___102_8143.FStar_Syntax_Syntax.sigattrs)
                       }), lbs2)
                 | uu____8152 ->
                     failwith
                       "impossible (typechecking should preserve Tm_let)"
                  in
               (match uu____8051 with
                | (se1,lbs1) ->
                    (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                       (FStar_List.iter
                          (fun lb  ->
                             let fv =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_TypeChecker_Env.insert_fv_info env1 fv
                               lb.FStar_Syntax_Syntax.lbtyp));
                     (let uu____8201 = log env1  in
                      if uu____8201
                      then
                        let uu____8202 =
                          let uu____8203 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs1)
                              (FStar_List.map
                                 (fun lb  ->
                                    let should_log =
                                      let uu____8218 =
                                        let uu____8227 =
                                          let uu____8228 =
                                            let uu____8231 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            uu____8231.FStar_Syntax_Syntax.fv_name
                                             in
                                          uu____8228.FStar_Syntax_Syntax.v
                                           in
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env1 uu____8227
                                         in
                                      match uu____8218 with
                                      | FStar_Pervasives_Native.None  -> true
                                      | uu____8238 -> false  in
                                    if should_log
                                    then
                                      let uu____8247 =
                                        FStar_Syntax_Print.lbname_to_string
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      let uu____8248 =
                                        FStar_Syntax_Print.term_to_string
                                          lb.FStar_Syntax_Syntax.lbtyp
                                         in
                                      FStar_Util.format2 "let %s : %s"
                                        uu____8247 uu____8248
                                    else ""))
                             in
                          FStar_All.pipe_right uu____8203
                            (FStar_String.concat "\n")
                           in
                        FStar_Util.print1 "%s\n" uu____8202
                      else ());
                     ([se1], []))))

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
             (fun uu___62_8300  ->
                match uu___62_8300 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____8301 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____8309) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____8315 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____8324 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____8329 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8344 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____8369 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8393) ->
          let uu____8402 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____8402
          then
            let for_export_bundle se1 uu____8437 =
              match uu____8437 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____8476,uu____8477) ->
                       let dec =
                         let uu___103_8487 = se1  in
                         let uu____8488 =
                           let uu____8489 =
                             let uu____8496 =
                               let uu____8499 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____8499  in
                             (l, us, uu____8496)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____8489  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____8488;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___103_8487.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___103_8487.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___103_8487.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____8511,uu____8512,uu____8513) ->
                       let dec =
                         let uu___104_8519 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___104_8519.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___104_8519.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___104_8519.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____8524 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____8546,uu____8547,uu____8548) ->
          let uu____8549 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____8549 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____8570 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____8570
          then
            ([(let uu___105_8586 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___105_8586.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___105_8586.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___105_8586.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____8588 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___63_8592  ->
                       match uu___63_8592 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____8593 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____8598 -> true
                       | uu____8599 -> false))
                in
             if uu____8588 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____8617 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____8622 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8627 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8632 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____8637 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____8655) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____8672 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____8672
          then ([], hidden)
          else
            (let dec =
               let uu____8689 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____8689;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____8704 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____8704
          then
            let uu____8713 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___106_8726 = se  in
                      let uu____8727 =
                        let uu____8728 =
                          let uu____8735 =
                            let uu____8736 =
                              let uu____8739 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____8739.FStar_Syntax_Syntax.fv_name  in
                            uu____8736.FStar_Syntax_Syntax.v  in
                          (uu____8735, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____8728  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____8727;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___106_8726.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___106_8726.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___106_8726.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____8713, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8763 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____8780 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____8795) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____8798 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8799 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____8809 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____8809) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____8810,uu____8811,uu____8812) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___64_8816  ->
                  match uu___64_8816 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____8817 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____8818,uu____8819) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___64_8827  ->
                  match uu___64_8827 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____8828 -> false))
          -> env
      | uu____8829 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____8897 se =
        match uu____8897 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____8950 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____8950
              then
                let uu____8951 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8951
              else ());
             (let uu____8953 = tc_decl env1 se  in
              match uu____8953 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____9003 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____9003
                             then
                               let uu____9004 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____9004
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
                    (let uu____9027 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____9027
                     then
                       let uu____9028 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____9034 =
                                  let uu____9035 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____9035 "\n"  in
                                Prims.strcat s uu____9034) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____9028
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____9040 =
                       let uu____9049 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____9049
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____9088 se1 =
                            match uu____9088 with
                            | (exports1,hidden1) ->
                                let uu____9116 = for_export hidden1 se1  in
                                (match uu____9116 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____9040 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___107_9195 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___107_9195.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___107_9195.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___107_9195.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___107_9195.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____9277 = acc  in
        match uu____9277 with
        | (uu____9312,uu____9313,env1,uu____9315) ->
            let uu____9328 =
              FStar_Util.record_time
                (fun uu____9374  -> process_one_decl acc se)
               in
            (match uu____9328 with
             | (r,ms_elapsed) ->
                 ((let uu____9438 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____9438
                   then
                     let uu____9439 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____9440 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____9439 uu____9440
                   else ());
                  r))
         in
      let uu____9442 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____9442 with
      | (ses1,exports,env1,uu____9490) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___108_9527 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___108_9527.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___108_9527.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___108_9527.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___108_9527.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___108_9527.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___108_9527.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___108_9527.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___108_9527.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___108_9527.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___108_9527.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___108_9527.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___108_9527.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___108_9527.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___108_9527.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___108_9527.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___108_9527.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___108_9527.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___108_9527.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___108_9527.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___108_9527.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___108_9527.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___108_9527.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___108_9527.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___108_9527.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___108_9527.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___108_9527.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___108_9527.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___108_9527.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___108_9527.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___108_9527.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___108_9527.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___108_9527.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___108_9527.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___108_9527.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____9544 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____9544 with
          | (univs2,t1) ->
              ((let uu____9552 =
                  let uu____9553 =
                    let uu____9558 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____9558  in
                  FStar_All.pipe_left uu____9553
                    (FStar_Options.Other "Exports")
                   in
                if uu____9552
                then
                  let uu____9559 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____9560 =
                    let uu____9561 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____9561
                      (FStar_String.concat ", ")
                     in
                  let uu____9570 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____9559 uu____9560 uu____9570
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____9573 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____9573 (fun a240  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____9599 =
             let uu____9600 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____9601 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____9600 uu____9601
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____9599);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9610) ->
              let uu____9619 =
                let uu____9620 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____9620  in
              if uu____9619
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____9630,uu____9631) ->
              let t =
                let uu____9643 =
                  let uu____9650 =
                    let uu____9651 =
                      let uu____9664 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____9664)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____9651  in
                  FStar_Syntax_Syntax.mk uu____9650  in
                uu____9643 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____9671,uu____9672,uu____9673) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____9681 =
                let uu____9682 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____9682  in
              if uu____9681 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____9686,lbs),uu____9688) ->
              let uu____9703 =
                let uu____9704 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____9704  in
              if uu____9703
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
              let uu____9723 =
                let uu____9724 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____9724  in
              if uu____9723
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____9731 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____9732 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____9739 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9740 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____9741 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____9742 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____9749 -> ()  in
        let uu____9750 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____9750 then () else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en  ->
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
             | FStar_Syntax_Syntax.Projector (l,uu____9845) -> true
             | uu____9846 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____9873 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____9904 ->
                   let uu____9905 =
                     let uu____9912 =
                       let uu____9913 =
                         let uu____9926 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____9926)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____9913  in
                     FStar_Syntax_Syntax.mk uu____9912  in
                   uu____9905 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____9934,uu____9935) ->
            let s1 =
              let uu___109_9945 = s  in
              let uu____9946 =
                let uu____9947 =
                  let uu____9954 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____9954)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____9947  in
              let uu____9955 =
                let uu____9958 =
                  let uu____9961 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____9961  in
                FStar_Syntax_Syntax.Assumption :: uu____9958  in
              {
                FStar_Syntax_Syntax.sigel = uu____9946;
                FStar_Syntax_Syntax.sigrng =
                  (uu___109_9945.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____9955;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___109_9945.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___109_9945.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____9964 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____9988 lbdef =
        match uu____9988 with
        | (uvs,t) ->
            let attrs =
              let uu____9999 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____9999
              then
                let uu____10002 =
                  let uu____10003 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____10003
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____10002 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___110_10005 = s  in
            let uu____10006 =
              let uu____10009 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____10009  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___110_10005.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____10006;
              FStar_Syntax_Syntax.sigmeta =
                (uu___110_10005.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____10025 -> failwith "Impossible!"  in
        let c_opt =
          let uu____10029 = FStar_Syntax_Util.is_unit t  in
          if uu____10029
          then
            let uu____10032 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____10032
          else
            (let uu____10034 =
               let uu____10035 = FStar_Syntax_Subst.compress t  in
               uu____10035.FStar_Syntax_Syntax.n  in
             match uu____10034 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____10040,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____10060 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____10069 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____10069
           then
             let uu____10070 =
               let uu____10071 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____10071 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____10070
           else
             (let uu____10079 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____10079))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____10090 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____10109 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____10126 ->
            failwith
              "Impossible! extract_interface: trying to extract splice"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_All.pipe_right sigelts
                (FStar_List.fold_left
                   (fun sigelts1  ->
                      fun s1  ->
                        match s1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (lid,uu____10170,uu____10171,uu____10172,uu____10173,uu____10174)
                            ->
                            ((let uu____10184 =
                                let uu____10187 =
                                  FStar_ST.op_Bang abstract_inductive_tycons
                                   in
                                lid :: uu____10187  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_tycons uu____10184);
                             (let uu____10288 = vals_of_abstract_inductive s1
                                 in
                              FStar_List.append uu____10288 sigelts1))
                        | FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____10292,uu____10293,uu____10294,uu____10295,uu____10296)
                            ->
                            ((let uu____10302 =
                                let uu____10305 =
                                  FStar_ST.op_Bang
                                    abstract_inductive_datacons
                                   in
                                lid :: uu____10305  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_datacons uu____10302);
                             sigelts1)
                        | uu____10406 ->
                            failwith
                              "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                   [])
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____10413 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____10413
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____10419 =
                   let uu___111_10420 = s  in
                   let uu____10421 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___111_10420.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___111_10420.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____10421;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___111_10420.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___111_10420.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____10419])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____10431 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____10431
            then []
            else
              (let uu____10435 = lbs  in
               match uu____10435 with
               | (flbs,slbs) ->
                   let typs_and_defs =
                     FStar_All.pipe_right slbs
                       (FStar_List.map
                          (fun lb  ->
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp),
                               (lb.FStar_Syntax_Syntax.lbdef))))
                      in
                   let is_lemma1 =
                     FStar_List.existsML
                       (fun uu____10510  ->
                          match uu____10510 with
                          | (uu____10521,t,uu____10523) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs_and_defs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____10547  ->
                            match uu____10547 with
                            | (u,t,d) -> val_of_lb s lid (u, t) d) lids
                       typs_and_defs
                      in
                   if
                     ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                        (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                       || is_lemma1
                   then vals
                   else
                     (let should_keep_defs =
                        FStar_List.existsML
                          (fun uu____10575  ->
                             match uu____10575 with
                             | (uu____10586,t,uu____10588) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs_and_defs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____10604,uu____10605) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____10610 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____10665 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                        in
                     FStar_Ident.lid_equals lid uu____10665) uu____10610
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____10668 =
                   let uu___112_10669 = s  in
                   let uu____10670 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___112_10669.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___112_10669.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____10670;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___112_10669.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___112_10669.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____10668]
               else [])
            else
              (let uu____10675 =
                 let uu___113_10676 = s  in
                 let uu____10677 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___113_10676.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___113_10676.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____10677;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___113_10676.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___113_10676.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____10675])
        | FStar_Syntax_Syntax.Sig_new_effect uu____10680 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10681 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____10682 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10683 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____10696 -> [s]  in
      let uu___114_10697 = m  in
      let uu____10698 =
        let uu____10699 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____10699 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___114_10697.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10698;
        FStar_Syntax_Syntax.exports =
          (uu___114_10697.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____10727 = FStar_Syntax_DsEnv.pop ()  in
       FStar_All.pipe_right uu____10727 (fun a241  -> ()));
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
      let uu___115_10742 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___115_10742.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___115_10742.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___115_10742.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___115_10742.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___115_10742.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___115_10742.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___115_10742.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___115_10742.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___115_10742.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___115_10742.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___115_10742.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___115_10742.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___115_10742.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___115_10742.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___115_10742.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___115_10742.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___115_10742.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___115_10742.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___115_10742.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___115_10742.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___115_10742.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___115_10742.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___115_10742.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___115_10742.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___115_10742.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___115_10742.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___115_10742.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___115_10742.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___115_10742.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___115_10742.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___115_10742.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___115_10742.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___115_10742.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___115_10742.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___115_10742.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___115_10742.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____10767 = FStar_Options.debug_any ()  in
       if uu____10767
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
         let uu___116_10772 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___116_10772.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___116_10772.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___116_10772.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___116_10772.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___116_10772.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___116_10772.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___116_10772.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___116_10772.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___116_10772.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___116_10772.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___116_10772.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___116_10772.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___116_10772.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___116_10772.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___116_10772.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___116_10772.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___116_10772.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___116_10772.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___116_10772.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___116_10772.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___116_10772.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___116_10772.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___116_10772.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___116_10772.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___116_10772.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___116_10772.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___116_10772.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___116_10772.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___116_10772.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___116_10772.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___116_10772.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___116_10772.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___116_10772.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___116_10772.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___116_10772.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____10774 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____10774 with
       | (ses,exports,env3) ->
           ((let uu___117_10807 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___117_10807.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___117_10807.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___117_10807.FStar_Syntax_Syntax.is_interface)
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
        let uu____10835 = tc_decls env decls  in
        match uu____10835 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___118_10866 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___118_10866.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___118_10866.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___118_10866.FStar_Syntax_Syntax.is_interface)
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
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env01 = push_context env0 msg  in
      let uu____10923 = tc_partial_modul env01 m  in
      match uu____10923 with
      | (modul,non_private_decls,env) ->
          finish_partial_modul false env modul non_private_decls

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
          let uu____10961 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____10961
          then
            let modul_iface = extract_interface en m  in
            ((let uu____10972 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low
                 in
              if uu____10972
              then
                let uu____10973 =
                  let uu____10974 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10974 then "" else " (in lax mode) "  in
                let uu____10976 =
                  let uu____10977 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10977
                  then
                    let uu____10978 =
                      let uu____10979 = FStar_Syntax_Print.modul_to_string m
                         in
                      Prims.strcat uu____10979 "\n"  in
                    Prims.strcat "\nfrom: " uu____10978
                  else ""  in
                let uu____10981 =
                  let uu____10982 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10982
                  then
                    let uu____10983 =
                      let uu____10984 =
                        FStar_Syntax_Print.modul_to_string modul_iface  in
                      Prims.strcat uu____10984 "\n"  in
                    Prims.strcat "\nto: " uu____10983
                  else ""  in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____10973
                  uu____10976 uu____10981
              else ());
             (let en0 =
                let en0 =
                  pop_context en
                    (Prims.strcat "Ending modul "
                       (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                let en01 =
                  let uu___119_10990 = en0  in
                  let uu____10991 =
                    let uu____11004 =
                      FStar_All.pipe_right
                        en.FStar_TypeChecker_Env.qtbl_name_and_index
                        FStar_Pervasives_Native.fst
                       in
                    (uu____11004, FStar_Pervasives_Native.None)  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___119_10990.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___119_10990.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___119_10990.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___119_10990.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___119_10990.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___119_10990.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___119_10990.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___119_10990.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___119_10990.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___119_10990.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___119_10990.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___119_10990.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___119_10990.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___119_10990.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___119_10990.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___119_10990.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___119_10990.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___119_10990.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___119_10990.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___119_10990.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___119_10990.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___119_10990.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___119_10990.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___119_10990.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___119_10990.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___119_10990.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___119_10990.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index = uu____10991;
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___119_10990.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___119_10990.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___119_10990.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___119_10990.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___119_10990.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___119_10990.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___119_10990.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___119_10990.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___119_10990.FStar_TypeChecker_Env.dep_graph)
                  }  in
                let uu____11041 =
                  let uu____11042 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____11042  in
                if uu____11041
                then
                  ((let uu____11044 =
                      FStar_Options.restore_cmd_line_options true  in
                    FStar_All.pipe_right uu____11044 (fun a242  -> ()));
                   z3_reset_options en01)
                else en01  in
              let uu____11046 = tc_modul en0 modul_iface  in
              match uu____11046 with
              | (modul_iface1,must_be_none,env) ->
                  if must_be_none <> FStar_Pervasives_Native.None
                  then
                    failwith
                      "Impossible! finish_partial_module: expected the second component to be None"
                  else
                    (((let uu___120_11092 = m  in
                       {
                         FStar_Syntax_Syntax.name =
                           (uu___120_11092.FStar_Syntax_Syntax.name);
                         FStar_Syntax_Syntax.declarations =
                           (uu___120_11092.FStar_Syntax_Syntax.declarations);
                         FStar_Syntax_Syntax.exports =
                           (modul_iface1.FStar_Syntax_Syntax.exports);
                         FStar_Syntax_Syntax.is_interface =
                           (uu___120_11092.FStar_Syntax_Syntax.is_interface)
                       })), (FStar_Pervasives_Native.Some modul_iface1), env)))
          else
            (let modul =
               let uu____11095 = FStar_Options.use_extracted_interfaces ()
                  in
               if uu____11095
               then
                 let uu___121_11096 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___121_11096.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___121_11096.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___121_11096.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___122_11098 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___122_11098.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___122_11098.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___122_11098.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____11101 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____11101 FStar_Util.smap_clear);
             (let uu____11129 =
                ((let uu____11132 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____11132) &&
                   (let uu____11134 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____11134))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____11129 then check_exports env modul exports else ());
             (let uu____11137 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____11137 (fun a243  -> ()));
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____11141 =
                let uu____11142 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____11142  in
              if uu____11141
              then
                let uu____11143 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____11143 (fun a244  -> ())
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
        let uu____11159 =
          let uu____11160 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____11160  in
        push_context env uu____11159  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____11179 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____11190 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____11190 with | (uu____11199,uu____11200,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____11225 = FStar_Options.debug_any ()  in
       if uu____11225
       then
         let uu____11226 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____11226
       else ());
      (let env1 =
         let uu___123_11230 = env  in
         let uu____11231 =
           let uu____11232 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____11232  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_11230.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_11230.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_11230.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_11230.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_11230.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_11230.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_11230.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_11230.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_11230.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_11230.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_11230.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_11230.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_11230.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_11230.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_11230.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_11230.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_11230.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_11230.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____11231;
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_11230.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___123_11230.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___123_11230.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___123_11230.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___123_11230.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_11230.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___123_11230.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_11230.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___123_11230.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___123_11230.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___123_11230.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___123_11230.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___123_11230.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___123_11230.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___123_11230.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___123_11230.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___123_11230.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___123_11230.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____11233 = tc_modul env1 m  in
       match uu____11233 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____11258 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____11258
             then
               let uu____11259 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____11259
             else ());
            (let uu____11262 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____11262
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
                       let uu____11301 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____11301 with
                       | (univnames1,e) ->
                           let uu___124_11308 = lb  in
                           let uu____11309 =
                             let uu____11312 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____11312 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___124_11308.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_11308.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___124_11308.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_11308.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____11309;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___124_11308.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___124_11308.FStar_Syntax_Syntax.lbpos)
                           }
                        in
                     let uu___125_11313 = se  in
                     let uu____11314 =
                       let uu____11315 =
                         let uu____11322 =
                           let uu____11329 = FStar_List.map update lbs  in
                           (b, uu____11329)  in
                         (uu____11322, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____11315  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____11314;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___125_11313.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___125_11313.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___125_11313.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___125_11313.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____11342 -> se  in
               let normalized_module =
                 let uu___126_11344 = m1  in
                 let uu____11345 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___126_11344.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____11345;
                   FStar_Syntax_Syntax.exports =
                     (uu___126_11344.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___126_11344.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____11346 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____11346
             else ());
            (m1, m_iface_opt, env2)))
  