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
      let uu____48 = FStar_Options.reuse_hint_for ()  in
      match uu____48 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____53 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____53 l  in
          let uu___359_54 = env  in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid  in (lid, uu____80)  in
              FStar_Pervasives_Native.Some uu____75  in
            (tbl, uu____68)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___359_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___359_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___359_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___359_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___359_54.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___359_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___359_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___359_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___359_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___359_54.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___359_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___359_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___359_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___359_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___359_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___359_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___359_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___359_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___359_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___359_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___359_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___359_54.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___359_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___359_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___359_54.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___359_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___359_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___359_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___359_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___359_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___359_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___359_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___359_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___359_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___359_54.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___359_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___359_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___359_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___359_54.FStar_TypeChecker_Env.dep_graph)
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
          let uu___360_104 = env  in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid  in (lid, uu____130)
                 in
              FStar_Pervasives_Native.Some uu____125  in
            (tbl, uu____118)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___360_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___360_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___360_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___360_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___360_104.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___360_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___360_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___360_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___360_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___360_104.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___360_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___360_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___360_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___360_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___360_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___360_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___360_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___360_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___360_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___360_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___360_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___360_104.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___360_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___360_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___360_104.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___360_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___360_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___360_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___360_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___360_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___360_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___360_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___360_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___360_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___360_104.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___360_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___360_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___360_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___360_104.FStar_TypeChecker_Env.dep_graph)
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
              open_univs_binders (Prims.parse_int "0")
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
                           let uu___361_456 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___361_456.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___361_456.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___361_456.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___361_456.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___361_456.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___361_456.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___361_456.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___361_456.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___361_456.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___361_456.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___361_456.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___361_456.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___361_456.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___361_456.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___361_456.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___361_456.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___361_456.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___361_456.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____478 ->
                               let op uu____508 =
                                 match uu____508 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____528 =
                                       let uu____529 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____538 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____529
                                         uu____538
                                        in
                                     (us, uu____528)
                                  in
                               let uu___362_547 = ed1  in
                               let uu____548 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____549 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____550 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____551 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____552 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____553 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____554 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____555 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____556 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____557 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____558 =
                                 let uu____559 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____559  in
                               let uu____570 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____571 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____572 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___363_580 = a  in
                                      let uu____581 =
                                        let uu____582 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____582
                                         in
                                      let uu____593 =
                                        let uu____594 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____594
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___363_580.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___363_580.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___363_580.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___363_580.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____581;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____593
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___362_547.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___362_547.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___362_547.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___362_547.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____548;
                                 FStar_Syntax_Syntax.bind_wp = uu____549;
                                 FStar_Syntax_Syntax.if_then_else = uu____550;
                                 FStar_Syntax_Syntax.ite_wp = uu____551;
                                 FStar_Syntax_Syntax.stronger = uu____552;
                                 FStar_Syntax_Syntax.close_wp = uu____553;
                                 FStar_Syntax_Syntax.assert_p = uu____554;
                                 FStar_Syntax_Syntax.assume_p = uu____555;
                                 FStar_Syntax_Syntax.null_wp = uu____556;
                                 FStar_Syntax_Syntax.trivial = uu____557;
                                 FStar_Syntax_Syntax.repr = uu____558;
                                 FStar_Syntax_Syntax.return_repr = uu____570;
                                 FStar_Syntax_Syntax.bind_repr = uu____571;
                                 FStar_Syntax_Syntax.actions = uu____572;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___362_547.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____639 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____644 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____639 uu____644  in
                           let uu____651 =
                             let uu____652 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____652.FStar_Syntax_Syntax.n  in
                           match uu____651 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____687)::(wp,uu____689)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____704 -> fail1 signature1)
                           | uu____705 -> fail1 signature1  in
                         let uu____706 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____706 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____730 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____737 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____737 with
                                     | (signature1,uu____749) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____750 ->
                                    let uu____753 =
                                      let uu____758 =
                                        let uu____759 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____759)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____758
                                       in
                                    (match uu____753 with
                                     | (uu____772,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____775 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____775
                                 in
                              ((let uu____777 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____777
                                then
                                  let uu____778 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____779 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____780 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____781 =
                                    let uu____782 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____782
                                     in
                                  let uu____783 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____778 uu____779 uu____780 uu____781
                                    uu____783
                                else ());
                               (let check_and_gen' env3 uu____815 k =
                                  match uu____815 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____851::uu____852 ->
                                           let uu____855 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____855 with
                                            | (us1,t1) ->
                                                let uu____878 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____878 with
                                                 | (us2,t2) ->
                                                     let uu____893 =
                                                       let uu____894 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____894 t2 k
                                                        in
                                                     let uu____895 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____895))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____914 =
                                      let uu____921 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____926 =
                                        let uu____933 =
                                          let uu____938 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____938
                                           in
                                        [uu____933]  in
                                      uu____921 :: uu____926  in
                                    let uu____951 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____914
                                      uu____951
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____955 = fresh_effect_signature ()
                                     in
                                  match uu____955 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____971 =
                                          let uu____978 =
                                            let uu____983 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____983
                                             in
                                          [uu____978]  in
                                        let uu____992 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____971
                                          uu____992
                                         in
                                      let expected_k =
                                        let uu____998 =
                                          let uu____1005 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____1010 =
                                            let uu____1017 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1022 =
                                              let uu____1029 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____1034 =
                                                let uu____1041 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1046 =
                                                  let uu____1053 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____1053]  in
                                                uu____1041 :: uu____1046  in
                                              uu____1029 :: uu____1034  in
                                            uu____1017 :: uu____1022  in
                                          uu____1005 :: uu____1010  in
                                        let uu____1082 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____998
                                          uu____1082
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____1095 =
                                      let uu____1098 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1098
                                       in
                                    let uu____1099 =
                                      let uu____1100 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1100
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1095
                                      uu____1099
                                     in
                                  let expected_k =
                                    let uu____1112 =
                                      let uu____1119 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1124 =
                                        let uu____1131 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____1136 =
                                          let uu____1143 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____1148 =
                                            let uu____1155 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1155]  in
                                          uu____1143 :: uu____1148  in
                                        uu____1131 :: uu____1136  in
                                      uu____1119 :: uu____1124  in
                                    let uu____1180 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1112
                                      uu____1180
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1195 =
                                      let uu____1202 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1207 =
                                        let uu____1214 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1214]  in
                                      uu____1202 :: uu____1207  in
                                    let uu____1231 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1195
                                      uu____1231
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____1235 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1235 with
                                  | (t,uu____1241) ->
                                      let expected_k =
                                        let uu____1245 =
                                          let uu____1252 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1257 =
                                            let uu____1264 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____1269 =
                                              let uu____1276 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____1276]  in
                                            uu____1264 :: uu____1269  in
                                          uu____1252 :: uu____1257  in
                                        let uu____1297 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____1245
                                          uu____1297
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____1310 =
                                      let uu____1313 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1313
                                       in
                                    let uu____1314 =
                                      let uu____1315 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1315
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1310
                                      uu____1314
                                     in
                                  let b_wp_a =
                                    let uu____1327 =
                                      let uu____1334 =
                                        let uu____1339 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1339
                                         in
                                      [uu____1334]  in
                                    let uu____1348 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1327
                                      uu____1348
                                     in
                                  let expected_k =
                                    let uu____1354 =
                                      let uu____1361 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1366 =
                                        let uu____1373 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1378 =
                                          let uu____1385 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1385]  in
                                        uu____1373 :: uu____1378  in
                                      uu____1361 :: uu____1366  in
                                    let uu____1406 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1354
                                      uu____1406
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1421 =
                                      let uu____1428 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1433 =
                                        let uu____1440 =
                                          let uu____1445 =
                                            let uu____1446 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1446
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1445
                                           in
                                        let uu____1455 =
                                          let uu____1462 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1462]  in
                                        uu____1440 :: uu____1455  in
                                      uu____1428 :: uu____1433  in
                                    let uu____1483 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1421
                                      uu____1483
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1498 =
                                      let uu____1505 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1510 =
                                        let uu____1517 =
                                          let uu____1522 =
                                            let uu____1523 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1523
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1522
                                           in
                                        let uu____1532 =
                                          let uu____1539 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1539]  in
                                        uu____1517 :: uu____1532  in
                                      uu____1505 :: uu____1510  in
                                    let uu____1560 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1498
                                      uu____1560
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1575 =
                                      let uu____1582 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1582]  in
                                    let uu____1595 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1575
                                      uu____1595
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1599 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1599 with
                                  | (t,uu____1605) ->
                                      let expected_k =
                                        let uu____1609 =
                                          let uu____1616 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1621 =
                                            let uu____1628 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1628]  in
                                          uu____1616 :: uu____1621  in
                                        let uu____1645 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1609
                                          uu____1645
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1648 =
                                  let uu____1661 =
                                    let uu____1662 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1662.FStar_Syntax_Syntax.n  in
                                  match uu____1661 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1681 ->
                                      let repr =
                                        let uu____1683 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1683 with
                                        | (t,uu____1689) ->
                                            let expected_k =
                                              let uu____1693 =
                                                let uu____1700 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1705 =
                                                  let uu____1712 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1712]  in
                                                uu____1700 :: uu____1705  in
                                              let uu____1729 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1693 uu____1729
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
                                        let uu____1746 =
                                          let uu____1753 =
                                            let uu____1754 =
                                              let uu____1769 =
                                                let uu____1778 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1785 =
                                                  let uu____1794 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1794]  in
                                                uu____1778 :: uu____1785  in
                                              (repr1, uu____1769)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1754
                                             in
                                          FStar_Syntax_Syntax.mk uu____1753
                                           in
                                        uu____1746
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1845 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1845 wp  in
                                      let destruct_repr t =
                                        let uu____1860 =
                                          let uu____1861 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1861.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1860 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1872,(t1,uu____1874)::
                                             (wp,uu____1876)::[])
                                            -> (t1, wp)
                                        | uu____1919 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1930 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1930
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1931 =
                                          fresh_effect_signature ()  in
                                        match uu____1931 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1947 =
                                                let uu____1954 =
                                                  let uu____1959 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1959
                                                   in
                                                [uu____1954]  in
                                              let uu____1968 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1947 uu____1968
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
                                              let uu____1974 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1974
                                               in
                                            let wp_g_x =
                                              let uu____1978 =
                                                let uu____1983 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1984 =
                                                  let uu____1985 =
                                                    let uu____1992 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1992
                                                     in
                                                  [uu____1985]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1983 uu____1984
                                                 in
                                              uu____1978
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____2019 =
                                                  let uu____2024 =
                                                    let uu____2025 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2025
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____2034 =
                                                    let uu____2035 =
                                                      let uu____2038 =
                                                        let uu____2041 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____2042 =
                                                          let uu____2045 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____2046 =
                                                            let uu____2049 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____2050 =
                                                              let uu____2053
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____2053]
                                                               in
                                                            uu____2049 ::
                                                              uu____2050
                                                             in
                                                          uu____2045 ::
                                                            uu____2046
                                                           in
                                                        uu____2041 ::
                                                          uu____2042
                                                         in
                                                      r :: uu____2038  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2035
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2024 uu____2034
                                                   in
                                                uu____2019
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____2069 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____2069
                                              then
                                                let uu____2076 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____2081 =
                                                  let uu____2088 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____2088]  in
                                                uu____2076 :: uu____2081
                                              else []  in
                                            let expected_k =
                                              let uu____2113 =
                                                let uu____2120 =
                                                  let uu____2127 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____2132 =
                                                    let uu____2139 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____2139]  in
                                                  uu____2127 :: uu____2132
                                                   in
                                                let uu____2156 =
                                                  let uu____2163 =
                                                    let uu____2170 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____2175 =
                                                      let uu____2182 =
                                                        let uu____2187 =
                                                          let uu____2188 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____2188
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____2187
                                                         in
                                                      let uu____2189 =
                                                        let uu____2196 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____2201 =
                                                          let uu____2208 =
                                                            let uu____2213 =
                                                              let uu____2214
                                                                =
                                                                let uu____2221
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____2221]
                                                                 in
                                                              let uu____2234
                                                                =
                                                                let uu____2237
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____2237
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____2214
                                                                uu____2234
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2213
                                                             in
                                                          [uu____2208]  in
                                                        uu____2196 ::
                                                          uu____2201
                                                         in
                                                      uu____2182 ::
                                                        uu____2189
                                                       in
                                                    uu____2170 :: uu____2175
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____2163
                                                   in
                                                FStar_List.append uu____2120
                                                  uu____2156
                                                 in
                                              let uu____2268 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2113 uu____2268
                                               in
                                            let uu____2271 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____2271 with
                                             | (expected_k1,uu____2279,uu____2280)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___364_2287 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_sig
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.gamma_sig);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.phase1
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.phase1);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.uvar_subtyping
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.uvar_subtyping);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___364_2287.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____2299 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____2299
                                           in
                                        let res =
                                          let wp =
                                            let uu____2306 =
                                              let uu____2311 =
                                                let uu____2312 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2312
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____2321 =
                                                let uu____2322 =
                                                  let uu____2325 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____2326 =
                                                    let uu____2329 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____2329]  in
                                                  uu____2325 :: uu____2326
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____2322
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____2311 uu____2321
                                               in
                                            uu____2306
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____2341 =
                                            let uu____2348 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____2353 =
                                              let uu____2360 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____2360]  in
                                            uu____2348 :: uu____2353  in
                                          let uu____2377 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____2341
                                            uu____2377
                                           in
                                        let uu____2380 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____2380 with
                                        | (expected_k1,uu____2388,uu____2389)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____2395 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____2395 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____2418 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____2431 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____2443 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____2443 with
                                               | (usubst,uvs) ->
                                                   let uu____2466 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____2467 =
                                                     let uu___365_2468 = act
                                                        in
                                                     let uu____2469 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____2470 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____2471 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___365_2468.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___365_2468.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____2469;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____2470;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____2471
                                                     }  in
                                                   (uu____2466, uu____2467))
                                             in
                                          match uu____2431 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____2475 =
                                                  let uu____2476 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____2476.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____2475 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____2498 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____2498
                                                    then
                                                      let uu____2499 =
                                                        let uu____2502 =
                                                          let uu____2503 =
                                                            let uu____2504 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2504
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____2503
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____2502
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____2499
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____2520 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____2521 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____2521 with
                                               | (act_typ1,uu____2529,g_t) ->
                                                   let env' =
                                                     let uu___366_2532 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___366_2532.FStar_TypeChecker_Env.dep_graph)
                                                     }  in
                                                   ((let uu____2534 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____2534
                                                     then
                                                       let uu____2535 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____2536 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____2537 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____2535
                                                         uu____2536
                                                         uu____2537
                                                     else ());
                                                    (let uu____2539 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____2539 with
                                                     | (act_defn,uu____2547,g_a)
                                                         ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant]
                                                             env3 act_defn
                                                            in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant;
                                                             FStar_TypeChecker_Normalize.Eager_unfolding;
                                                             FStar_TypeChecker_Normalize.Beta]
                                                             env3 act_typ1
                                                            in
                                                         let uu____2551 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____2583
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____2583
                                                                with
                                                                | (bs1,uu____2595)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____2602
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2602
                                                                     in
                                                                    let uu____2605
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____2605
                                                                    with
                                                                    | 
                                                                    (k1,uu____2619,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____2623 ->
                                                               let uu____2624
                                                                 =
                                                                 let uu____2629
                                                                   =
                                                                   let uu____2630
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____2631
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____2630
                                                                    uu____2631
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____2629)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____2624
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____2551
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____2646
                                                                  =
                                                                  let uu____2647
                                                                    =
                                                                    let uu____2648
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____2648
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____2647
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____2646);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____2650
                                                                    =
                                                                    let uu____2651
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____2651.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____2650
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____2672
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____2672
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____2679
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____2679
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____2699
                                                                    =
                                                                    let uu____2700
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____2700]
                                                                     in
                                                                    let uu____2701
                                                                    =
                                                                    let uu____2710
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____2710]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2699;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2701;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____2729
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2729))
                                                                  | uu____2732
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____2733
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
                                                                    let uu____2753
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____2753))
                                                                   in
                                                                match uu____2733
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
                                                                    let uu___367_2772
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___367_2772.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___367_2772.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___367_2772.FStar_Syntax_Syntax.action_params);
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
                                match uu____1648 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____2796 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____2796
                                       in
                                    let uu____2799 =
                                      let uu____2804 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____2804 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____2823 ->
                                               let uu____2826 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____2832 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____2832 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____2826
                                               then (gen_univs, t)
                                               else
                                                 (let uu____2838 =
                                                    let uu____2843 =
                                                      let uu____2844 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____2845 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____2844 uu____2845
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____2843)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____2838
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____2799 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____2853 =
                                             let uu____2864 =
                                               let uu____2865 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____2865.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____2864)  in
                                           match uu____2853 with
                                           | ([],uu____2874) -> t
                                           | (uu____2885,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____2886,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____2916 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____2939 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____2939
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____2946 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____2948 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____2948))
                                                && (m <> n1)
                                               in
                                            if uu____2946
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____2966 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2973 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2974 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2966 uu____2973
                                                  uu____2974
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2986 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2986 with
                                           | (univs2,defn) ->
                                               let uu____3001 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____3001 with
                                                | (univs',typ) ->
                                                    let uu___368_3017 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___368_3017.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___368_3017.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___368_3017.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___369_3020 = ed2  in
                                           let uu____3021 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____3022 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____3023 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____3024 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____3025 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____3026 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____3027 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____3028 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____3029 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____3030 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____3031 =
                                             let uu____3032 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____3032
                                              in
                                           let uu____3049 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____3050 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____3051 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___369_3020.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___369_3020.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____3021;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____3022;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____3023;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____3024;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____3025;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____3026;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____3027;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____3028;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____3029;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____3030;
                                             FStar_Syntax_Syntax.repr =
                                               uu____3031;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____3049;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____3050;
                                             FStar_Syntax_Syntax.actions =
                                               uu____3051;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___369_3020.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____3055 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____3055
                                           then
                                             let uu____3056 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____3056
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
      let uu____3078 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____3078 with
      | (effect_binders_un,signature_un) ->
          let uu____3095 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3095 with
           | (effect_binders,env1,uu____3114) ->
               let uu____3115 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3115 with
                | (signature,uu____3131) ->
                    let raise_error1 uu____3146 =
                      match uu____3146 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3172  ->
                           match uu____3172 with
                           | (bv,qual) ->
                               let uu____3183 =
                                 let uu___370_3184 = bv  in
                                 let uu____3185 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___370_3184.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___370_3184.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3185
                                 }  in
                               (uu____3183, qual)) effect_binders
                       in
                    let uu____3188 =
                      let uu____3195 =
                        let uu____3196 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3196.FStar_Syntax_Syntax.n  in
                      match uu____3195 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3206)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3228 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3188 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3252 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3252
                           then
                             let uu____3253 =
                               let uu____3256 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3256  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3253
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3296 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3296 with
                           | (t2,comp,uu____3309) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3318 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____3318 with
                          | (repr,_comp) ->
                              ((let uu____3340 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3340
                                then
                                  let uu____3341 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3341
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
                                let uu____3345 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____3347 =
                                    let uu____3348 =
                                      let uu____3349 =
                                        let uu____3364 =
                                          let uu____3373 =
                                            let uu____3380 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____3383 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____3380, uu____3383)  in
                                          [uu____3373]  in
                                        (wp_type, uu____3364)  in
                                      FStar_Syntax_Syntax.Tm_app uu____3349
                                       in
                                    mk1 uu____3348  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____3347
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____3418 =
                                      let uu____3423 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____3423)  in
                                    let uu____3424 =
                                      let uu____3431 =
                                        let uu____3436 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____3436
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____3431]  in
                                    uu____3418 :: uu____3424  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____3462 =
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
                                  let uu____3521 = item  in
                                  match uu____3521 with
                                  | (u_item,item1) ->
                                      let uu____3536 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____3536 with
                                       | (item2,item_comp) ->
                                           ((let uu____3552 =
                                               let uu____3553 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____3553
                                                in
                                             if uu____3552
                                             then
                                               let uu____3554 =
                                                 let uu____3559 =
                                                   let uu____3560 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____3561 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____3560 uu____3561
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____3559)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____3554
                                             else ());
                                            (let uu____3563 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____3563 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____3581 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____3582 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____3583 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____3583 with
                                | (dmff_env1,uu____3607,bind_wp,bind_elab) ->
                                    let uu____3610 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____3610 with
                                     | (dmff_env2,uu____3634,return_wp,return_elab)
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
                                           let uu____3643 =
                                             let uu____3644 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____3644.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3643 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____3690 =
                                                 let uu____3705 =
                                                   let uu____3710 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____3710
                                                    in
                                                 match uu____3705 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____3768 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____3690 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____3809 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____3809 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____3826 =
                                                          let uu____3827 =
                                                            let uu____3842 =
                                                              let uu____3851
                                                                =
                                                                let uu____3858
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____3861
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3858,
                                                                  uu____3861)
                                                                 in
                                                              [uu____3851]
                                                               in
                                                            (wp_type,
                                                              uu____3842)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3827
                                                           in
                                                        mk1 uu____3826  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____3886 =
                                                      let uu____3895 =
                                                        let uu____3896 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____3896
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____3895
                                                       in
                                                    (match uu____3886 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____3919
                                                           =
                                                           let error_msg =
                                                             let uu____3921 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____3922 =
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
                                                               uu____3921
                                                               uu____3922
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
                                                               ((let uu____3927
                                                                   =
                                                                   let uu____3928
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____3928
                                                                    in
                                                                 if
                                                                   uu____3927
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____3930
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
                                                                   uu____3930
                                                                   (fun a236 
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
                                                             let uu____3955 =
                                                               let uu____3960
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____3961
                                                                 =
                                                                 let uu____3962
                                                                   =
                                                                   let uu____3969
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____3969,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____3962]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____3960
                                                                 uu____3961
                                                                in
                                                             uu____3955
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____3996 =
                                                             let uu____3997 =
                                                               let uu____4004
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4004]
                                                                in
                                                             b11 ::
                                                               uu____3997
                                                              in
                                                           let uu____4021 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____3996
                                                             uu____4021
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4024 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4030 =
                                             let uu____4031 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4031.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4030 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4077 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4077
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4092 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4098 =
                                             let uu____4099 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4099.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4098 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____4128 =
                                                 let uu____4129 =
                                                   let uu____4136 =
                                                     let uu____4141 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4141
                                                      in
                                                   [uu____4136]  in
                                                 FStar_List.append uu____4129
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____4128 body what
                                           | uu____4154 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____4176 =
                                                let uu____4177 =
                                                  let uu____4178 =
                                                    let uu____4193 =
                                                      let uu____4202 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4202
                                                       in
                                                    (t, uu____4193)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4178
                                                   in
                                                mk1 uu____4177  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4176)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4244 = f a2  in
                                               [uu____4244]
                                           | x::xs ->
                                               let uu____4249 =
                                                 apply_last1 f xs  in
                                               x :: uu____4249
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
                                           let uu____4275 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____4275 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____4305 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____4305
                                                 then
                                                   let uu____4306 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____4306
                                                 else ());
                                                (let uu____4308 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____4308))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____4317 =
                                                 let uu____4322 = mk_lid name
                                                    in
                                                 let uu____4323 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____4322 uu____4323
                                                  in
                                               (match uu____4317 with
                                                | (sigelt,fv) ->
                                                    ((let uu____4327 =
                                                        let uu____4330 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____4330
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____4327);
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
                                          (let uu____4435 =
                                             let uu____4438 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____4439 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____4438 :: uu____4439  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____4435);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____4545 =
                                               let uu____4548 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____4549 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____4548 :: uu____4549  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____4545);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____4652 =
                                                FStar_List.fold_left
                                                  (fun uu____4692  ->
                                                     fun action  ->
                                                       match uu____4692 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____4713 =
                                                             let uu____4720 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____4720
                                                               params_un
                                                              in
                                                           (match uu____4713
                                                            with
                                                            | (action_params,env',uu____4729)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____4749
                                                                     ->
                                                                    match uu____4749
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____4760
                                                                    =
                                                                    let uu___371_4761
                                                                    = bv  in
                                                                    let uu____4762
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___371_4761.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___371_4761.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____4762
                                                                    }  in
                                                                    (uu____4760,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____4766
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____4766
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
                                                                    uu____4802
                                                                    ->
                                                                    let uu____4803
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____4803
                                                                     in
                                                                    ((
                                                                    let uu____4807
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____4807
                                                                    then
                                                                    let uu____4808
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____4809
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____4810
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____4811
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____4808
                                                                    uu____4809
                                                                    uu____4810
                                                                    uu____4811
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
                                                                    let uu____4815
                                                                    =
                                                                    let uu____4818
                                                                    =
                                                                    let uu___372_4819
                                                                    = action
                                                                     in
                                                                    let uu____4820
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____4821
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___372_4819.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___372_4819.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___372_4819.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____4820;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____4821
                                                                    }  in
                                                                    uu____4818
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____4815))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____4652 with
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
                                                      let uu____4860 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____4865 =
                                                        let uu____4872 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____4872]  in
                                                      uu____4860 ::
                                                        uu____4865
                                                       in
                                                    let uu____4889 =
                                                      let uu____4892 =
                                                        let uu____4893 =
                                                          let uu____4894 =
                                                            let uu____4909 =
                                                              let uu____4918
                                                                =
                                                                let uu____4925
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____4928
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4925,
                                                                  uu____4928)
                                                                 in
                                                              [uu____4918]
                                                               in
                                                            (repr,
                                                              uu____4909)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4894
                                                           in
                                                        mk1 uu____4893  in
                                                      let uu____4953 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____4892
                                                        uu____4953
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____4889
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____4954 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____4956 =
                                                    let uu____4965 =
                                                      let uu____4966 =
                                                        let uu____4969 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____4969
                                                         in
                                                      uu____4966.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____4965 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____4983)
                                                        ->
                                                        let uu____5012 =
                                                          let uu____5029 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____5029
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____5081 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____5012
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____5133 =
                                                               let uu____5134
                                                                 =
                                                                 let uu____5137
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5137
                                                                  in
                                                               uu____5134.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____5133
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____5166
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____5166
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____5181
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5206
                                                                     ->
                                                                    match uu____5206
                                                                    with
                                                                    | 
                                                                    (bv,uu____5212)
                                                                    ->
                                                                    let uu____5213
                                                                    =
                                                                    let uu____5214
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5214
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5213
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____5181
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
                                                                    let uu____5280
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____5280
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____5285
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____5293
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____5293
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____5298
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____5301
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____5298,
                                                                    uu____5301)))
                                                              | uu____5312 ->
                                                                  let uu____5313
                                                                    =
                                                                    let uu____5318
                                                                    =
                                                                    let uu____5319
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____5319
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____5318)
                                                                     in
                                                                  raise_error1
                                                                    uu____5313))
                                                    | uu____5328 ->
                                                        let uu____5329 =
                                                          let uu____5334 =
                                                            let uu____5335 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____5335
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____5334)
                                                           in
                                                        raise_error1
                                                          uu____5329
                                                     in
                                                  (match uu____4956 with
                                                   | (pre,post) ->
                                                       ((let uu____5365 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____5367 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____5369 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___373_5371
                                                             = ed  in
                                                           let uu____5372 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____5373 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____5374 =
                                                             let uu____5375 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____5375)
                                                              in
                                                           let uu____5382 =
                                                             let uu____5383 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____5383)
                                                              in
                                                           let uu____5390 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____5391 =
                                                             let uu____5392 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____5392)
                                                              in
                                                           let uu____5399 =
                                                             let uu____5400 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____5400)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____5372;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____5373;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____5374;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____5382;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____5390;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____5391;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____5399;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___373_5371.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____5407 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____5407
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____5425
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____5425
                                                               then
                                                                 let uu____5426
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____5426
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
                                                                    let uu____5438
                                                                    =
                                                                    let uu____5441
                                                                    =
                                                                    let uu____5442
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____5442)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5441
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
                                                                    uu____5438;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____5449
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____5449
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____5451
                                                                 =
                                                                 let uu____5454
                                                                   =
                                                                   let uu____5457
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____5457
                                                                    in
                                                                 FStar_List.append
                                                                   uu____5454
                                                                   sigelts'
                                                                  in
                                                               (uu____5451,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____5523 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____5523 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____5558 = FStar_List.hd ses  in
            uu____5558.FStar_Syntax_Syntax.sigrng  in
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
           | uu____5563 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____5567,[],t,uu____5569,uu____5570);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____5572;
               FStar_Syntax_Syntax.sigattrs = uu____5573;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____5575,_t_top,_lex_t_top,_0_16,uu____5578);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____5580;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____5581;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____5583,_t_cons,_lex_t_cons,_0_17,uu____5586);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____5588;
                 FStar_Syntax_Syntax.sigattrs = uu____5589;_}::[]
               when
               ((_0_16 = (Prims.parse_int "0")) &&
                  (_0_17 = (Prims.parse_int "0")))
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
                 let uu____5634 =
                   let uu____5641 =
                     let uu____5642 =
                       let uu____5649 =
                         let uu____5652 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____5652
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____5649, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____5642  in
                   FStar_Syntax_Syntax.mk uu____5641  in
                 uu____5634 FStar_Pervasives_Native.None r1  in
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
                   let uu____5668 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5668
                    in
                 let hd1 =
                   let uu____5670 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5670
                    in
                 let tl1 =
                   let uu____5672 =
                     let uu____5673 =
                       let uu____5680 =
                         let uu____5681 =
                           let uu____5688 =
                             let uu____5691 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____5691
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____5688, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____5681  in
                       FStar_Syntax_Syntax.mk uu____5680  in
                     uu____5673 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5672
                    in
                 let res =
                   let uu____5700 =
                     let uu____5707 =
                       let uu____5708 =
                         let uu____5715 =
                           let uu____5718 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____5718
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____5715,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____5708  in
                     FStar_Syntax_Syntax.mk uu____5707  in
                   uu____5700 FStar_Pervasives_Native.None r2  in
                 let uu____5724 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____5724
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
               let uu____5747 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____5747;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____5752 ->
               let err_msg =
                 let uu____5756 =
                   let uu____5757 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____5757  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____5756
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun uu____5779  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____5779 with
          | (uvs,t) ->
              let uu____5792 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____5792 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____5803 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____5803 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____5820 =
                        let uu____5823 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____5823
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____5820)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____5845 =
          let uu____5846 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____5846 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____5845 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____5870 =
          let uu____5871 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____5871 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____5870 r
  
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
          let uu____5919 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____5919 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____5950 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____5950 FStar_List.flatten  in
              ((let uu____5964 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____5966 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____5966)
                   in
                if uu____5964
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
                          let uu____5977 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____5987,uu____5988,uu____5989,uu____5990,uu____5991)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____6000 -> failwith "Impossible!"  in
                          match uu____5977 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____6013 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____6017,uu____6018,uu____6019,uu____6020,uu____6021)
                        -> lid
                    | uu____6030 -> failwith "Impossible"  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let res =
                  let uu____6043 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____6043
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
                (let uu____6065 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____6072 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____6072 en  in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun se  ->
    let comb f1 f2 =
      match (f1, f2) with
      | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
         (e2,l2)) ->
          FStar_Pervasives_Native.Some
            ((FStar_List.append e1 e2), (l1 || l2))
      | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some (e, l)
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l)) ->
          FStar_Pervasives_Native.Some (e, l)
      | uu____6302 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____6350 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____6350 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____6369 .
    'Auu____6369 FStar_Pervasives_Native.option -> 'Auu____6369 Prims.list
  =
  fun uu___353_6378  ->
    match uu___353_6378 with
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
      match l1 with
      | [] -> FStar_Pervasives_Native.None
      | uu____6422 ->
          let rec collect1 l =
            match l with
            | [] -> []
            | hd1::tl1 ->
                let uu____6454 = collect1 tl1  in
                (match uu____6454 with
                 | [] -> [(hd1, (Prims.parse_int "1"))]
                 | (h,n1)::t ->
                     if h = hd1
                     then (h, (n1 + (Prims.parse_int "1"))) :: t
                     else (hd1, (Prims.parse_int "1")) :: (h, n1) :: t)
             in
          let summ l =
            let l3 = FStar_List.sortWith (fun x  -> fun y  -> x - y) l  in
            collect1 l3  in
          let l11 = summ l1  in
          let l21 = summ l2  in
          let rec aux l12 l22 =
            match (l12, l22) with
            | ([],[]) -> FStar_Pervasives_Native.None
            | ((e,n1)::uu____6639,[]) ->
                FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
            | ([],(e,n1)::uu____6674) ->
                FStar_Pervasives_Native.Some (e, (Prims.parse_int "0"), n1)
            | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 <> hd2 ->
                FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
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
      (let uu____6848 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____6848
       then
         let uu____6849 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____6849
       else ());
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let uu____6852 = get_fail_se se  in
       match uu____6852 with
       | FStar_Pervasives_Native.Some (uu____6869,false ) when
           let uu____6880 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____6880 -> ([], [])
       | FStar_Pervasives_Native.Some (errnos,uu____6886) ->
           ((let uu____6898 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____6898
             then
               let uu____6899 =
                 let uu____6900 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____6900
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____6899
             else ());
            (let errs =
               FStar_Errors.catch_errors
                 (fun uu____6918  -> tc_decl' env1 se)
                in
             (let uu____6920 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____6920
              then
                (FStar_Util.print_string ">> Got issues:\n";
                 FStar_List.iter FStar_Errors.print_issue errs;
                 FStar_Util.print_string ">> //Got issues:\n")
              else ());
             (let uu____6924 =
                let uu____6939 =
                  let uu____6948 =
                    FStar_List.concatMap
                      (fun i  -> list_of_option i.FStar_Errors.issue_number)
                      errs
                     in
                  check_multi_contained errnos uu____6948  in
                (errs, uu____6939)  in
              match uu____6924 with
              | ([],uu____6971) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   FStar_Errors.raise_error
                     (FStar_Errors.Error_DidNotFail,
                       "This top-level definition was expected to fail, but it succeeded")
                     se.FStar_Syntax_Syntax.sigrng)
              | (uu____6999,FStar_Pervasives_Native.Some (e,n1,n2)) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   (let uu____7022 =
                      let uu____7027 =
                        let uu____7028 = FStar_Util.string_of_int e  in
                        let uu____7029 = FStar_Util.string_of_int n1  in
                        let uu____7030 = FStar_Util.string_of_int n2  in
                        FStar_Util.format3
                          "This top-level definition was expected to raise Error #%s %s times, but it raised it %s times"
                          uu____7028 uu____7029 uu____7030
                         in
                      (FStar_Errors.Error_DidNotFail, uu____7027)  in
                    FStar_Errors.raise_error uu____7022
                      se.FStar_Syntax_Syntax.sigrng))
              | (uu____7039,FStar_Pervasives_Native.None ) -> ([], []))))
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
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7087 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7112 ->
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
            let uu____7167 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1)
               in
            if uu____7167
            then
              let ses1 =
                let uu____7173 =
                  let uu____7174 =
                    let uu____7175 =
                      tc_inductive
                        (let uu___374_7184 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___374_7184.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___374_7184.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___374_7184.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___374_7184.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___374_7184.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___374_7184.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___374_7184.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___374_7184.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___374_7184.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___374_7184.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___374_7184.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___374_7184.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___374_7184.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___374_7184.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___374_7184.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___374_7184.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___374_7184.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___374_7184.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___374_7184.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___374_7184.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 = true;
                           FStar_TypeChecker_Env.failhard =
                             (uu___374_7184.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___374_7184.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___374_7184.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___374_7184.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___374_7184.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___374_7184.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___374_7184.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___374_7184.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___374_7184.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___374_7184.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___374_7184.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___374_7184.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___374_7184.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___374_7184.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___374_7184.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___374_7184.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___374_7184.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___374_7184.FStar_TypeChecker_Env.dep_graph)
                         }) ses se.FStar_Syntax_Syntax.sigquals lids
                       in
                    FStar_All.pipe_right uu____7175
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____7174
                    (FStar_TypeChecker_Normalize.elim_uvars env1)
                   in
                FStar_All.pipe_right uu____7173
                  FStar_Syntax_Util.ses_of_sigbundle
                 in
              ((let uu____7196 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____7196
                then
                  let uu____7197 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___375_7200 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___375_7200.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___375_7200.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___375_7200.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___375_7200.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Inductive after phase 1: %s\n"
                    uu____7197
                else ());
               ses1)
            else ses  in
          let uu____7207 =
            tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
          (match uu____7207 with
           | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p r; ([se], []))
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
          let uu____7239 = cps_and_elaborate env ne  in
          (match uu____7239 with
           | (ses,ne1,lift_from_pure_opt) ->
               let effect_and_lift_ses =
                 match lift_from_pure_opt with
                 | FStar_Pervasives_Native.Some lift ->
                     [(let uu___376_7276 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___376_7276.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___376_7276.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___376_7276.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___376_7276.FStar_Syntax_Syntax.sigattrs)
                       });
                     lift]
                 | FStar_Pervasives_Native.None  ->
                     [(let uu___377_7278 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___377_7278.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___377_7278.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___377_7278.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___377_7278.FStar_Syntax_Syntax.sigattrs)
                       })]
                  in
               ([], (FStar_List.append ses effect_and_lift_ses)))
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let ne1 =
            let uu____7285 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env)
               in
            if uu____7285
            then
              let ne1 =
                let uu____7287 =
                  let uu____7288 =
                    let uu____7289 =
                      tc_eff_decl
                        (let uu___378_7292 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___378_7292.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___378_7292.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___378_7292.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___378_7292.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___378_7292.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___378_7292.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___378_7292.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___378_7292.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___378_7292.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___378_7292.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___378_7292.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___378_7292.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___378_7292.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___378_7292.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___378_7292.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___378_7292.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___378_7292.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___378_7292.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___378_7292.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___378_7292.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 = true;
                           FStar_TypeChecker_Env.failhard =
                             (uu___378_7292.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___378_7292.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___378_7292.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___378_7292.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___378_7292.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___378_7292.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___378_7292.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___378_7292.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___378_7292.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___378_7292.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___378_7292.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___378_7292.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___378_7292.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___378_7292.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___378_7292.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___378_7292.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___378_7292.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___378_7292.FStar_TypeChecker_Env.dep_graph)
                         }) ne
                       in
                    FStar_All.pipe_right uu____7289
                      (fun ne1  ->
                         let uu___379_7296 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ne1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___379_7296.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___379_7296.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___379_7296.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___379_7296.FStar_Syntax_Syntax.sigattrs)
                         })
                     in
                  FStar_All.pipe_right uu____7288
                    (FStar_TypeChecker_Normalize.elim_uvars env)
                   in
                FStar_All.pipe_right uu____7287
                  FStar_Syntax_Util.eff_decl_of_new_effect
                 in
              ((let uu____7298 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____7298
                then
                  let uu____7299 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___380_7302 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___380_7302.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___380_7302.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___380_7302.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___380_7302.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Effect decl after phase 1: %s\n"
                    uu____7299
                else ());
               ne1)
            else ne  in
          let ne2 = tc_eff_decl env ne1  in
          let se1 =
            let uu___381_7307 = se  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_new_effect ne2);
              FStar_Syntax_Syntax.sigrng =
                (uu___381_7307.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals =
                (uu___381_7307.FStar_Syntax_Syntax.sigquals);
              FStar_Syntax_Syntax.sigmeta =
                (uu___381_7307.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___381_7307.FStar_Syntax_Syntax.sigattrs)
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
          let uu____7315 =
            let uu____7322 =
              FStar_TypeChecker_Env.lookup_effect_lid env
                sub1.FStar_Syntax_Syntax.source
               in
            monad_signature env sub1.FStar_Syntax_Syntax.source uu____7322
             in
          (match uu____7315 with
           | (a,wp_a_src) ->
               let uu____7337 =
                 let uu____7344 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7344
                  in
               (match uu____7337 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7360 =
                        let uu____7363 =
                          let uu____7364 =
                            let uu____7371 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7371)  in
                          FStar_Syntax_Syntax.NT uu____7364  in
                        [uu____7363]  in
                      FStar_Syntax_Subst.subst uu____7360 wp_b_tgt  in
                    let expected_k =
                      let uu____7379 =
                        let uu____7386 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7391 =
                          let uu____7398 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7398]  in
                        uu____7386 :: uu____7391  in
                      let uu____7415 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7379 uu____7415  in
                    let repr_type eff_name a1 wp =
                      let no_reify l =
                        let uu____7444 =
                          let uu____7449 =
                            FStar_Util.format1 "Effect %s cannot be reified"
                              l.FStar_Ident.str
                             in
                          (FStar_Errors.Fatal_EffectCannotBeReified,
                            uu____7449)
                           in
                        let uu____7450 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error uu____7444 uu____7450  in
                      let uu____7453 =
                        FStar_TypeChecker_Env.effect_decl_opt env eff_name
                         in
                      match uu____7453 with
                      | FStar_Pervasives_Native.None  -> no_reify eff_name
                      | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                          let repr =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [FStar_Syntax_Syntax.U_unknown] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr))
                             in
                          let uu____7487 =
                            let uu____7488 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            Prims.op_Negation uu____7488  in
                          if uu____7487
                          then no_reify eff_name
                          else
                            (let uu____7494 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____7495 =
                               let uu____7502 =
                                 let uu____7503 =
                                   let uu____7518 =
                                     let uu____7527 =
                                       FStar_Syntax_Syntax.as_arg a1  in
                                     let uu____7534 =
                                       let uu____7543 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____7543]  in
                                     uu____7527 :: uu____7534  in
                                   (repr, uu____7518)  in
                                 FStar_Syntax_Syntax.Tm_app uu____7503  in
                               FStar_Syntax_Syntax.mk uu____7502  in
                             uu____7495 FStar_Pervasives_Native.None
                               uu____7494)
                       in
                    let uu____7581 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____7753 =
                            if
                              (FStar_List.length uvs) > (Prims.parse_int "0")
                            then
                              let uu____7762 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____7762 with
                              | (usubst,uvs1) ->
                                  let uu____7785 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____7786 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____7785, uu____7786)
                            else (env, lift_wp)  in
                          (match uu____7753 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if
                                   (FStar_List.length uvs) =
                                     (Prims.parse_int "0")
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____7831 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____7831))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____7902 =
                            if
                              (FStar_List.length what) >
                                (Prims.parse_int "0")
                            then
                              let uu____7915 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____7915 with
                              | (usubst,uvs) ->
                                  let uu____7940 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____7940)
                            else ([], lift)  in
                          (match uu____7902 with
                           | (uvs,lift1) ->
                               ((let uu____7975 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7975
                                 then
                                   let uu____7976 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____7976
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____7979 =
                                   let uu____7986 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____7986 lift1
                                    in
                                 match uu____7979 with
                                 | (lift2,comp,uu____8011) ->
                                     let uu____8012 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8012 with
                                      | (uu____8041,lift_wp,lift_elab) ->
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
                                              (Prims.parse_int "0")
                                          then
                                            let uu____8068 =
                                              let uu____8079 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8079
                                               in
                                            let uu____8096 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8068, uu____8096)
                                          else
                                            (let uu____8124 =
                                               let uu____8135 =
                                                 let uu____8144 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8144)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8135
                                                in
                                             let uu____8159 =
                                               let uu____8168 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8168)  in
                                             (uu____8124, uu____8159))))))
                       in
                    (match uu____7581 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___382_8240 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___382_8240.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___382_8240.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___382_8240.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___382_8240.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___382_8240.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___382_8240.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___382_8240.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___382_8240.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___382_8240.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___382_8240.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___382_8240.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___382_8240.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___382_8240.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___382_8240.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___382_8240.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___382_8240.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___382_8240.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___382_8240.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___382_8240.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___382_8240.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___382_8240.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___382_8240.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___382_8240.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___382_8240.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___382_8240.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___382_8240.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___382_8240.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___382_8240.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___382_8240.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___382_8240.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___382_8240.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___382_8240.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___382_8240.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___382_8240.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___382_8240.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___382_8240.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___382_8240.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___382_8240.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___382_8240.FStar_TypeChecker_Env.dep_graph)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8272 =
                                 let uu____8277 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8277 with
                                 | (usubst,uvs1) ->
                                     let uu____8300 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8301 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8300, uu____8301)
                                  in
                               (match uu____8272 with
                                | (env2,lift2) ->
                                    let uu____8306 =
                                      let uu____8313 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8313
                                       in
                                    (match uu____8306 with
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
                                             let uu____8339 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8340 =
                                               let uu____8347 =
                                                 let uu____8348 =
                                                   let uu____8363 =
                                                     let uu____8372 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8379 =
                                                       let uu____8388 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8388]  in
                                                     uu____8372 :: uu____8379
                                                      in
                                                   (lift_wp1, uu____8363)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8348
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8347
                                                in
                                             uu____8340
                                               FStar_Pervasives_Native.None
                                               uu____8339
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8429 =
                                             let uu____8436 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8441 =
                                               let uu____8448 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8453 =
                                                 let uu____8460 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8460]  in
                                               uu____8448 :: uu____8453  in
                                             uu____8436 :: uu____8441  in
                                           let uu____8481 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8429
                                             uu____8481
                                            in
                                         let uu____8484 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8484 with
                                          | (expected_k2,uu____8494,uu____8495)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    (Prims.parse_int "0")
                                                then
                                                  check_and_gen env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____8499 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8499))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8507 =
                             let uu____8508 =
                               let uu____8509 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8509
                                 FStar_List.length
                                in
                             uu____8508 <> (Prims.parse_int "1")  in
                           if uu____8507
                           then
                             let uu____8528 =
                               let uu____8533 =
                                 let uu____8534 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8535 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8536 =
                                   let uu____8537 =
                                     let uu____8538 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8538
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8537
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8534 uu____8535 uu____8536
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8533)
                                in
                             FStar_Errors.raise_error uu____8528 r
                           else ());
                          (let uu____8559 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8561 =
                                  let uu____8562 =
                                    let uu____8565 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8565
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8562
                                    FStar_List.length
                                   in
                                uu____8561 <> (Prims.parse_int "1"))
                              in
                           if uu____8559
                           then
                             let uu____8600 =
                               let uu____8605 =
                                 let uu____8606 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8607 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8608 =
                                   let uu____8609 =
                                     let uu____8610 =
                                       let uu____8613 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____8613
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8610
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8609
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8606 uu____8607 uu____8608
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8605)
                                in
                             FStar_Errors.raise_error uu____8600 r
                           else ());
                          (let sub2 =
                             let uu___383_8650 = sub1  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___383_8650.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___383_8650.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp =
                                 (FStar_Pervasives_Native.Some lift_wp);
                               FStar_Syntax_Syntax.lift = lift1
                             }  in
                           let se1 =
                             let uu___384_8652 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___384_8652.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___384_8652.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___384_8652.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___384_8652.FStar_Syntax_Syntax.sigattrs)
                             }  in
                           ([se1], []))))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
          let env0 = env  in
          let uu____8667 =
            if (FStar_List.length uvs) = (Prims.parse_int "0")
            then (env, uvs, tps, c)
            else
              (let uu____8691 = FStar_Syntax_Subst.univ_var_opening uvs  in
               match uu____8691 with
               | (usubst,uvs1) ->
                   let tps1 = FStar_Syntax_Subst.subst_binders usubst tps  in
                   let c1 =
                     let uu____8722 =
                       FStar_Syntax_Subst.shift_subst
                         (FStar_List.length tps1) usubst
                        in
                     FStar_Syntax_Subst.subst_comp uu____8722 c  in
                   let uu____8729 =
                     FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                   (uu____8729, uvs1, tps1, c1))
             in
          (match uu____8667 with
           | (env1,uvs1,tps1,c1) ->
               let env2 = FStar_TypeChecker_Env.set_range env1 r  in
               let uu____8749 = FStar_Syntax_Subst.open_comp tps1 c1  in
               (match uu____8749 with
                | (tps2,c2) ->
                    let uu____8764 =
                      FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                    (match uu____8764 with
                     | (tps3,env3,us) ->
                         let uu____8782 =
                           FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                         (match uu____8782 with
                          | (c3,u,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env3
                                 g;
                               (let tps4 =
                                  FStar_Syntax_Subst.close_binders tps3  in
                                let c4 =
                                  FStar_Syntax_Subst.close_comp tps4 c3  in
                                let uu____8803 =
                                  let uu____8804 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_arrow
                                         (tps4, c4))
                                      FStar_Pervasives_Native.None r
                                     in
                                  FStar_TypeChecker_Util.generalize_universes
                                    env0 uu____8804
                                   in
                                match uu____8803 with
                                | (uvs2,t) ->
                                    let uu____8831 =
                                      let uu____8836 =
                                        let uu____8847 =
                                          let uu____8848 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____8848.FStar_Syntax_Syntax.n
                                           in
                                        (tps4, uu____8847)  in
                                      match uu____8836 with
                                      | ([],FStar_Syntax_Syntax.Tm_arrow
                                         (uu____8861,c5)) -> ([], c5)
                                      | (uu____8893,FStar_Syntax_Syntax.Tm_arrow
                                         (tps5,c5)) -> (tps5, c5)
                                      | uu____8924 ->
                                          failwith
                                            "Impossible (t is an arrow)"
                                       in
                                    (match uu____8831 with
                                     | (tps5,c5) ->
                                         (if
                                            (FStar_List.length uvs2) <>
                                              (Prims.parse_int "1")
                                          then
                                            (let uu____8950 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 uvs2 t
                                                in
                                             match uu____8950 with
                                             | (uu____8955,t1) ->
                                                 let uu____8957 =
                                                   let uu____8962 =
                                                     let uu____8963 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid
                                                        in
                                                     let uu____8964 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs2)
                                                         FStar_Util.string_of_int
                                                        in
                                                     let uu____8965 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t1
                                                        in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       uu____8963 uu____8964
                                                       uu____8965
                                                      in
                                                   (FStar_Errors.Fatal_TooManyUniverse,
                                                     uu____8962)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____8957 r)
                                          else ();
                                          (let se1 =
                                             let uu___385_8968 = se  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                    (lid, uvs2, tps5, c5,
                                                      flags1));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___385_8968.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___385_8968.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___385_8968.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___385_8968.FStar_Syntax_Syntax.sigattrs)
                                             }  in
                                           ([se1], []))))))))))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____8975,uu____8976,uu____8977) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___354_8981  ->
                  match uu___354_8981 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____8982 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_let (uu____8987,uu____8988) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___354_8996  ->
                  match uu___354_8996 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____8997 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          ((let uu____9007 = FStar_TypeChecker_Env.lid_exists env1 lid  in
            if uu____9007
            then
              let uu____9008 =
                let uu____9013 =
                  let uu____9014 = FStar_Ident.text_of_lid lid  in
                  FStar_Util.format1
                    "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                    uu____9014
                   in
                (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                  uu____9013)
                 in
              FStar_Errors.raise_error uu____9008 r
            else ());
           (let uu____9016 =
              let uu____9025 =
                (FStar_Options.use_two_phase_tc ()) &&
                  (FStar_TypeChecker_Env.should_verify env1)
                 in
              if uu____9025
              then
                let uu____9034 =
                  tc_declare_typ
                    (let uu___386_9037 = env1  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___386_9037.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___386_9037.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___386_9037.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___386_9037.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___386_9037.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___386_9037.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___386_9037.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___386_9037.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___386_9037.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___386_9037.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___386_9037.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___386_9037.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___386_9037.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___386_9037.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___386_9037.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___386_9037.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___386_9037.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___386_9037.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___386_9037.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___386_9037.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___386_9037.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___386_9037.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___386_9037.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___386_9037.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___386_9037.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___386_9037.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___386_9037.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___386_9037.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___386_9037.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___386_9037.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___386_9037.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___386_9037.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___386_9037.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___386_9037.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___386_9037.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___386_9037.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___386_9037.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___386_9037.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___386_9037.FStar_TypeChecker_Env.dep_graph)
                     }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                   in
                match uu____9034 with
                | (uvs1,t1) ->
                    ((let uu____9061 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____9061
                      then
                        let uu____9062 = FStar_Syntax_Print.term_to_string t1
                           in
                        let uu____9063 =
                          FStar_Syntax_Print.univ_names_to_string uvs1  in
                        FStar_Util.print2
                          "Val declaration after phase 1: %s and uvs: %s\n"
                          uu____9062 uu____9063
                      else ());
                     (uvs1, t1))
              else (uvs, t)  in
            match uu____9016 with
            | (uvs1,t1) ->
                let uu____9092 =
                  tc_declare_typ env1 (uvs1, t1)
                    se.FStar_Syntax_Syntax.sigrng
                   in
                (match uu____9092 with
                 | (uvs2,t2) ->
                     ([(let uu___387_9120 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___387_9120.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___387_9120.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___387_9120.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___387_9120.FStar_Syntax_Syntax.sigattrs)
                        })], []))))
      | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let uu____9125 =
            let uu____9134 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1)
               in
            if uu____9134
            then
              let uu____9143 =
                tc_assume
                  (let uu___388_9146 = env1  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___388_9146.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___388_9146.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___388_9146.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___388_9146.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___388_9146.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___388_9146.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___388_9146.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___388_9146.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___388_9146.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___388_9146.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___388_9146.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___388_9146.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___388_9146.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___388_9146.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___388_9146.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___388_9146.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___388_9146.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___388_9146.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___388_9146.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___388_9146.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 = true;
                     FStar_TypeChecker_Env.failhard =
                       (uu___388_9146.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___388_9146.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___388_9146.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___388_9146.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___388_9146.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___388_9146.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___388_9146.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___388_9146.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___388_9146.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___388_9146.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___388_9146.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___388_9146.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___388_9146.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___388_9146.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___388_9146.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___388_9146.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___388_9146.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.dep_graph =
                       (uu___388_9146.FStar_TypeChecker_Env.dep_graph)
                   }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                 in
              match uu____9143 with
              | (uvs1,t1) ->
                  ((let uu____9170 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____9170
                    then
                      let uu____9171 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____9172 =
                        FStar_Syntax_Print.univ_names_to_string uvs1  in
                      FStar_Util.print2
                        "Assume after phase 1: %s and uvs: %s\n" uu____9171
                        uu____9172
                    else ());
                   (uvs1, t1))
            else (uvs, t)  in
          (match uu____9125 with
           | (uvs1,t1) ->
               let uu____9201 =
                 tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
               (match uu____9201 with
                | (uvs2,t2) ->
                    ([(let uu___389_9229 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___389_9229.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___389_9229.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___389_9229.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___389_9229.FStar_Syntax_Syntax.sigattrs)
                       })], [])))
      | FStar_Syntax_Syntax.Sig_main e ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let env2 =
            FStar_TypeChecker_Env.set_expected_typ env1
              FStar_Syntax_Syntax.t_unit
             in
          let uu____9233 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
          (match uu____9233 with
           | (e1,c,g1) ->
               let uu____9251 =
                 let uu____9258 =
                   let uu____9261 =
                     FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                      in
                   FStar_Pervasives_Native.Some uu____9261  in
                 let uu____9262 =
                   let uu____9267 = FStar_Syntax_Syntax.lcomp_comp c  in
                   (e1, uu____9267)  in
                 FStar_TypeChecker_TcTerm.check_expected_effect env2
                   uu____9258 uu____9262
                  in
               (match uu____9251 with
                | (e2,uu____9277,g) ->
                    ((let uu____9280 = FStar_TypeChecker_Env.conj_guard g1 g
                         in
                      FStar_TypeChecker_Rel.force_trivial_guard env2
                        uu____9280);
                     (let se1 =
                        let uu___390_9282 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_main e2);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___390_9282.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___390_9282.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___390_9282.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___390_9282.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      ([se1], [])))))
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          ((let uu____9294 = FStar_Options.debug_any ()  in
            if uu____9294
            then
              let uu____9295 =
                FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                 in
              let uu____9296 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.print2 "%s: Found splice of (%s)\n" uu____9295
                uu____9296
            else ());
           (let ses = env.FStar_TypeChecker_Env.splice env t  in
            let lids' =
              FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
            FStar_List.iter
              (fun lid  ->
                 let uu____9309 =
                   FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                 match uu____9309 with
                 | FStar_Pervasives_Native.Some uu____9312 -> ()
                 | FStar_Pervasives_Native.None  ->
                     let uu____9313 =
                       let uu____9318 =
                         let uu____9319 = FStar_Ident.string_of_lid lid  in
                         let uu____9320 =
                           let uu____9321 =
                             FStar_List.map FStar_Ident.string_of_lid lids'
                              in
                           FStar_All.pipe_left (FStar_String.concat ", ")
                             uu____9321
                            in
                         FStar_Util.format2
                           "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                           uu____9319 uu____9320
                          in
                       (FStar_Errors.Fatal_SplicedUndef, uu____9318)  in
                     FStar_Errors.raise_error uu____9313 r) lids;
            ([], ses)))
      | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let check_quals_eq l qopt q =
            match qopt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some q
            | FStar_Pervasives_Native.Some q' ->
                let drop_logic =
                  FStar_List.filter
                    (fun x  ->
                       Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                   in
                let uu____9393 =
                  let uu____9402 = drop_logic q  in
                  let uu____9405 = drop_logic q'  in (uu____9402, uu____9405)
                   in
                (match uu____9393 with
                 | (q1,q'1) ->
                     let uu____9426 =
                       ((FStar_List.length q1) = (FStar_List.length q'1)) &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal q1 q'1)
                        in
                     if uu____9426
                     then FStar_Pervasives_Native.Some q1
                     else
                       (let uu____9434 =
                          let uu____9439 =
                            let uu____9440 =
                              FStar_Syntax_Print.lid_to_string l  in
                            let uu____9441 =
                              FStar_Syntax_Print.quals_to_string q1  in
                            let uu____9442 =
                              FStar_Syntax_Print.quals_to_string q'1  in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____9440 uu____9441 uu____9442
                             in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____9439)
                           in
                        FStar_Errors.raise_error uu____9434 r))
             in
          let rename_parameters lb =
            let rename_in_typ def typ =
              let typ1 = FStar_Syntax_Subst.compress typ  in
              let def_bs =
                let uu____9474 =
                  let uu____9475 = FStar_Syntax_Subst.compress def  in
                  uu____9475.FStar_Syntax_Syntax.n  in
                match uu____9474 with
                | FStar_Syntax_Syntax.Tm_abs (binders,uu____9485,uu____9486)
                    -> binders
                | uu____9507 -> []  in
              match typ1 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                    (val_bs,c);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars = uu____9517;_} ->
                  let has_auto_name bv =
                    FStar_Util.starts_with
                      (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      FStar_Ident.reserved_prefix
                     in
                  let rec rename_binders1 def_bs1 val_bs1 =
                    match (def_bs1, val_bs1) with
                    | ([],uu____9601) -> val_bs1
                    | (uu____9624,[]) -> val_bs1
                    | ((body_bv,uu____9648)::bt,(val_bv,aqual)::vt) ->
                        let uu____9685 = rename_binders1 bt vt  in
                        ((match ((has_auto_name body_bv),
                                  (has_auto_name val_bv))
                          with
                          | (true ,uu____9701) -> (val_bv, aqual)
                          | (false ,true ) ->
                              ((let uu___391_9703 = val_bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (let uu___392_9706 =
                                       val_bv.FStar_Syntax_Syntax.ppname  in
                                     {
                                       FStar_Ident.idText =
                                         ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                       FStar_Ident.idRange =
                                         (uu___392_9706.FStar_Ident.idRange)
                                     });
                                  FStar_Syntax_Syntax.index =
                                    (uu___391_9703.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort =
                                    (uu___391_9703.FStar_Syntax_Syntax.sort)
                                }), aqual)
                          | (false ,false ) -> (val_bv, aqual))) ::
                          uu____9685
                     in
                  let uu____9707 =
                    let uu____9714 =
                      let uu____9715 =
                        let uu____9728 = rename_binders1 def_bs val_bs  in
                        (uu____9728, c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____9715  in
                    FStar_Syntax_Syntax.mk uu____9714  in
                  uu____9707 FStar_Pervasives_Native.None r1
              | uu____9746 -> typ1  in
            let uu___393_9747 = lb  in
            let uu____9748 =
              rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                lb.FStar_Syntax_Syntax.lbtyp
               in
            {
              FStar_Syntax_Syntax.lbname =
                (uu___393_9747.FStar_Syntax_Syntax.lbname);
              FStar_Syntax_Syntax.lbunivs =
                (uu___393_9747.FStar_Syntax_Syntax.lbunivs);
              FStar_Syntax_Syntax.lbtyp = uu____9748;
              FStar_Syntax_Syntax.lbeff =
                (uu___393_9747.FStar_Syntax_Syntax.lbeff);
              FStar_Syntax_Syntax.lbdef =
                (uu___393_9747.FStar_Syntax_Syntax.lbdef);
              FStar_Syntax_Syntax.lbattrs =
                (uu___393_9747.FStar_Syntax_Syntax.lbattrs);
              FStar_Syntax_Syntax.lbpos =
                (uu___393_9747.FStar_Syntax_Syntax.lbpos)
            }  in
          let uu____9751 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.fold_left
                 (fun uu____9802  ->
                    fun lb  ->
                      match uu____9802 with
                      | (gen1,lbs1,quals_opt) ->
                          let lbname =
                            FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                             in
                          let uu____9844 =
                            let uu____9855 =
                              FStar_TypeChecker_Env.try_lookup_val_decl env1
                                (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            match uu____9855 with
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
                                  | uu____9928 ->
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
                                 (let uu____9971 =
                                    FStar_Syntax_Syntax.mk_lb
                                      ((FStar_Util.Inr lbname), uvs,
                                        FStar_Parser_Const.effect_ALL_lid,
                                        tval, def,
                                        (lb.FStar_Syntax_Syntax.lbpos))
                                     in
                                  (false, uu____9971, quals_opt1)))
                             in
                          (match uu____9844 with
                           | (gen2,lb1,quals_opt1) ->
                               (gen2, (lb1 :: lbs1), quals_opt1)))
                 (true, [],
                   (if se.FStar_Syntax_Syntax.sigquals = []
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (se.FStar_Syntax_Syntax.sigquals))))
             in
          (match uu____9751 with
           | (should_generalize,lbs',quals_opt) ->
               let quals =
                 match quals_opt with
                 | FStar_Pervasives_Native.None  ->
                     [FStar_Syntax_Syntax.Visible_default]
                 | FStar_Pervasives_Native.Some q ->
                     let uu____10059 =
                       FStar_All.pipe_right q
                         (FStar_Util.for_some
                            (fun uu___355_10063  ->
                               match uu___355_10063 with
                               | FStar_Syntax_Syntax.Irreducible  -> true
                               | FStar_Syntax_Syntax.Visible_default  -> true
                               | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                               | uu____10064 -> false))
                        in
                     if uu____10059
                     then q
                     else FStar_Syntax_Syntax.Visible_default :: q
                  in
               let lbs'1 = FStar_List.rev lbs'  in
               let e =
                 let uu____10074 =
                   let uu____10081 =
                     let uu____10082 =
                       let uu____10095 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_constant
                              FStar_Const.Const_unit)
                           FStar_Pervasives_Native.None r
                          in
                       (((FStar_Pervasives_Native.fst lbs), lbs'1),
                         uu____10095)
                        in
                     FStar_Syntax_Syntax.Tm_let uu____10082  in
                   FStar_Syntax_Syntax.mk uu____10081  in
                 uu____10074 FStar_Pervasives_Native.None r  in
               let env0 =
                 let uu___394_10114 = env1  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___394_10114.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___394_10114.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___394_10114.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___394_10114.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___394_10114.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___394_10114.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___394_10114.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___394_10114.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___394_10114.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___394_10114.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___394_10114.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___394_10114.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize = should_generalize;
                   FStar_TypeChecker_Env.letrecs =
                     (uu___394_10114.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = true;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___394_10114.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___394_10114.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___394_10114.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___394_10114.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___394_10114.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___394_10114.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___394_10114.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___394_10114.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___394_10114.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___394_10114.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___394_10114.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___394_10114.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___394_10114.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___394_10114.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___394_10114.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___394_10114.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___394_10114.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___394_10114.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___394_10114.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___394_10114.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___394_10114.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___394_10114.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___394_10114.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___394_10114.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___394_10114.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let e1 =
                 let uu____10116 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env0)
                    in
                 if uu____10116
                 then
                   let drop_lbtyp e_lax =
                     let uu____10123 =
                       let uu____10124 = FStar_Syntax_Subst.compress e_lax
                          in
                       uu____10124.FStar_Syntax_Syntax.n  in
                     match uu____10123 with
                     | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                         let lb_unannotated =
                           let uu____10142 =
                             let uu____10143 = FStar_Syntax_Subst.compress e
                                in
                             uu____10143.FStar_Syntax_Syntax.n  in
                           match uu____10142 with
                           | FStar_Syntax_Syntax.Tm_let
                               ((uu____10146,lb1::[]),uu____10148) ->
                               let uu____10161 =
                                 let uu____10162 =
                                   FStar_Syntax_Subst.compress
                                     lb1.FStar_Syntax_Syntax.lbtyp
                                    in
                                 uu____10162.FStar_Syntax_Syntax.n  in
                               uu____10161 = FStar_Syntax_Syntax.Tm_unknown
                           | uu____10165 ->
                               failwith
                                 "Impossible: first phase lb and second phase lb differ in structure!"
                            in
                         if lb_unannotated
                         then
                           let uu___395_10166 = e_lax  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false,
                                     [(let uu___396_10178 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           FStar_Syntax_Syntax.tun;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbdef);
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___396_10178.FStar_Syntax_Syntax.lbpos)
                                       })]), e2));
                             FStar_Syntax_Syntax.pos =
                               (uu___395_10166.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___395_10166.FStar_Syntax_Syntax.vars)
                           }
                         else e_lax
                     | uu____10180 -> e_lax  in
                   let e1 =
                     let uu____10182 =
                       let uu____10183 =
                         let uu____10184 =
                           FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                             (let uu___397_10193 = env0  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___397_10193.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___397_10193.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___397_10193.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___397_10193.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___397_10193.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___397_10193.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___397_10193.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___397_10193.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___397_10193.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___397_10193.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___397_10193.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___397_10193.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___397_10193.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___397_10193.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___397_10193.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___397_10193.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___397_10193.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___397_10193.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___397_10193.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___397_10193.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___397_10193.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___397_10193.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___397_10193.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___397_10193.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___397_10193.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___397_10193.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___397_10193.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___397_10193.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___397_10193.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___397_10193.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___397_10193.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___397_10193.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___397_10193.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___397_10193.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___397_10193.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___397_10193.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___397_10193.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___397_10193.FStar_TypeChecker_Env.dep_graph)
                              }) e
                            in
                         FStar_All.pipe_right uu____10184
                           (fun uu____10204  ->
                              match uu____10204 with
                              | (e1,uu____10212,uu____10213) -> e1)
                          in
                       FStar_All.pipe_right uu____10183
                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                            env0)
                        in
                     FStar_All.pipe_right uu____10182 drop_lbtyp  in
                   ((let uu____10215 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____10215
                     then
                       let uu____10216 = FStar_Syntax_Print.term_to_string e1
                          in
                       FStar_Util.print1 "Let binding after phase 1: %s\n"
                         uu____10216
                     else ());
                    e1)
                 else e  in
               let uu____10219 =
                 let uu____10230 =
                   FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                    in
                 match uu____10230 with
                 | ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                        (lbs1,e2);
                      FStar_Syntax_Syntax.pos = uu____10249;
                      FStar_Syntax_Syntax.vars = uu____10250;_},uu____10251,g)
                     when FStar_TypeChecker_Env.is_trivial g ->
                     let lbs2 =
                       let uu____10278 =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs1)
                           (FStar_List.map rename_parameters)
                          in
                       ((FStar_Pervasives_Native.fst lbs1), uu____10278)  in
                     let quals1 =
                       match e2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_meta
                           (uu____10296,FStar_Syntax_Syntax.Meta_desugared
                            (FStar_Syntax_Syntax.Masked_effect ))
                           -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                       | uu____10301 -> quals  in
                     ((let uu___398_10309 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___398_10309.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___398_10309.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___398_10309.FStar_Syntax_Syntax.sigattrs)
                       }), lbs2)
                 | uu____10312 ->
                     failwith
                       "impossible (typechecking should preserve Tm_let)"
                  in
               (match uu____10219 with
                | (se1,lbs1) ->
                    (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                       (FStar_List.iter
                          (fun lb  ->
                             let fv =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_TypeChecker_Env.insert_fv_info env1 fv
                               lb.FStar_Syntax_Syntax.lbtyp));
                     (let uu____10361 = log env1  in
                      if uu____10361
                      then
                        let uu____10362 =
                          let uu____10363 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs1)
                              (FStar_List.map
                                 (fun lb  ->
                                    let should_log =
                                      let uu____10378 =
                                        let uu____10387 =
                                          let uu____10388 =
                                            let uu____10391 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            uu____10391.FStar_Syntax_Syntax.fv_name
                                             in
                                          uu____10388.FStar_Syntax_Syntax.v
                                           in
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env1 uu____10387
                                         in
                                      match uu____10378 with
                                      | FStar_Pervasives_Native.None  -> true
                                      | uu____10398 -> false  in
                                    if should_log
                                    then
                                      let uu____10407 =
                                        FStar_Syntax_Print.lbname_to_string
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      let uu____10408 =
                                        FStar_Syntax_Print.term_to_string
                                          lb.FStar_Syntax_Syntax.lbtyp
                                         in
                                      FStar_Util.format2 "let %s : %s"
                                        uu____10407 uu____10408
                                    else ""))
                             in
                          FStar_All.pipe_right uu____10363
                            (FStar_String.concat "\n")
                           in
                        FStar_Util.print1 "%s\n" uu____10362
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
             (fun uu___356_10460  ->
                match uu___356_10460 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____10461 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____10469) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____10475 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____10484 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____10489 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____10504 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____10529 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10553) ->
          let uu____10562 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10562
          then
            let for_export_bundle se1 uu____10597 =
              match uu____10597 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____10636,uu____10637) ->
                       let dec =
                         let uu___399_10647 = se1  in
                         let uu____10648 =
                           let uu____10649 =
                             let uu____10656 =
                               let uu____10657 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____10657  in
                             (l, us, uu____10656)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____10649
                            in
                         {
                           FStar_Syntax_Syntax.sigel = uu____10648;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___399_10647.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___399_10647.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___399_10647.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____10667,uu____10668,uu____10669) ->
                       let dec =
                         let uu___400_10675 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___400_10675.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___400_10675.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___400_10675.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____10680 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____10702,uu____10703,uu____10704)
          ->
          let uu____10705 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10705 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____10726 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____10726
          then
            ([(let uu___401_10742 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___401_10742.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___401_10742.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___401_10742.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____10744 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___357_10748  ->
                       match uu___357_10748 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____10749 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____10754 ->
                           true
                       | uu____10755 -> false))
                in
             if uu____10744 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____10773 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____10778 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10783 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10788 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10793 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10811) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10822 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____10822
          then ([], hidden)
          else
            (let dec =
               let uu____10839 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____10839;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____10850 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10850
          then
            let uu____10859 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___402_10872 = se  in
                      let uu____10873 =
                        let uu____10874 =
                          let uu____10881 =
                            let uu____10882 =
                              let uu____10885 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____10885.FStar_Syntax_Syntax.fv_name  in
                            uu____10882.FStar_Syntax_Syntax.v  in
                          (uu____10881, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____10874  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____10873;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___402_10872.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___402_10872.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___402_10872.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____10859, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____10905 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____10922 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____10937) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____10940 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10941 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____10951 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____10951) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____10952,uu____10953,uu____10954) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___358_10958  ->
                  match uu___358_10958 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10959 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____10960,uu____10961) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___358_10969  ->
                  match uu___358_10969 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10970 -> false))
          -> env
      | uu____10971 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____11039 se =
        match uu____11039 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____11092 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____11092
              then
                let uu____11093 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____11093
              else ());
             (let uu____11095 = tc_decl env1 se  in
              match uu____11095 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____11145 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____11145
                             then
                               let uu____11146 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____11146
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
                    (let uu____11169 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____11169
                     then
                       let uu____11170 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____11176 =
                                  let uu____11177 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____11177 "\n"  in
                                Prims.strcat s uu____11176) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____11170
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____11182 =
                       let uu____11191 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____11191
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____11230 se1 =
                            match uu____11230 with
                            | (exports1,hidden1) ->
                                let uu____11258 = for_export hidden1 se1  in
                                (match uu____11258 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____11182 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___403_11337 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___403_11337.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___403_11337.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___403_11337.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___403_11337.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____11419 = acc  in
        match uu____11419 with
        | (uu____11454,uu____11455,env1,uu____11457) ->
            let uu____11470 =
              FStar_Util.record_time
                (fun uu____11516  -> process_one_decl acc se)
               in
            (match uu____11470 with
             | (r,ms_elapsed) ->
                 ((let uu____11580 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____11580
                   then
                     let uu____11581 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____11582 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____11581 uu____11582
                   else ());
                  r))
         in
      let uu____11584 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____11584 with
      | (ses1,exports,env1,uu____11632) ->
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
          let uu___404_11669 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___404_11669.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___404_11669.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___404_11669.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___404_11669.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___404_11669.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___404_11669.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___404_11669.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___404_11669.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___404_11669.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___404_11669.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___404_11669.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___404_11669.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___404_11669.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___404_11669.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___404_11669.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___404_11669.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___404_11669.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___404_11669.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___404_11669.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___404_11669.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___404_11669.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___404_11669.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___404_11669.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___404_11669.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___404_11669.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___404_11669.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___404_11669.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___404_11669.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___404_11669.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___404_11669.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___404_11669.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___404_11669.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___404_11669.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___404_11669.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___404_11669.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___404_11669.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___404_11669.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____11686 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____11686 with
          | (univs2,t1) ->
              ((let uu____11694 =
                  let uu____11695 =
                    let uu____11700 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____11700  in
                  FStar_All.pipe_left uu____11695
                    (FStar_Options.Other "Exports")
                   in
                if uu____11694
                then
                  let uu____11701 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____11702 =
                    let uu____11703 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____11703
                      (FStar_String.concat ", ")
                     in
                  let uu____11714 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____11701 uu____11702 uu____11714
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____11717 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____11717 (fun a237  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____11743 =
             let uu____11744 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____11745 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____11744 uu____11745
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____11743);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11754) ->
              let uu____11763 =
                let uu____11764 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11764  in
              if uu____11763
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____11774,uu____11775) ->
              let t =
                let uu____11787 =
                  let uu____11794 =
                    let uu____11795 =
                      let uu____11808 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____11808)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____11795  in
                  FStar_Syntax_Syntax.mk uu____11794  in
                uu____11787 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____11825,uu____11826,uu____11827) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____11835 =
                let uu____11836 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11836  in
              if uu____11835 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____11840,lbs),uu____11842) ->
              let uu____11851 =
                let uu____11852 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11852  in
              if uu____11851
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
              let uu____11871 =
                let uu____11872 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11872  in
              if uu____11871
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____11887 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____11888 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11895 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11896 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____11897 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____11898 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____11905 -> ()  in
        let uu____11906 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____11906 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____12001) -> true
             | uu____12002 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____12029 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____12060 ->
                   let uu____12061 =
                     let uu____12068 =
                       let uu____12069 =
                         let uu____12082 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____12082)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12069  in
                     FStar_Syntax_Syntax.mk uu____12068  in
                   uu____12061 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____12100,uu____12101) ->
            let s1 =
              let uu___405_12111 = s  in
              let uu____12112 =
                let uu____12113 =
                  let uu____12120 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____12120)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____12113  in
              let uu____12121 =
                let uu____12124 =
                  let uu____12127 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____12127  in
                FStar_Syntax_Syntax.Assumption :: uu____12124  in
              {
                FStar_Syntax_Syntax.sigel = uu____12112;
                FStar_Syntax_Syntax.sigrng =
                  (uu___405_12111.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____12121;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___405_12111.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___405_12111.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____12130 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____12154 lbdef =
        match uu____12154 with
        | (uvs,t) ->
            let attrs =
              let uu____12165 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____12165
              then
                let uu____12168 =
                  let uu____12169 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____12169
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____12168 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___406_12171 = s  in
            let uu____12172 =
              let uu____12175 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____12175  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___406_12171.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____12172;
              FStar_Syntax_Syntax.sigmeta =
                (uu___406_12171.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____12191 -> failwith "Impossible!"  in
        let c_opt =
          let uu____12197 = FStar_Syntax_Util.is_unit t  in
          if uu____12197
          then
            let uu____12202 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____12202
          else
            (let uu____12208 =
               let uu____12209 = FStar_Syntax_Subst.compress t  in
               uu____12209.FStar_Syntax_Syntax.n  in
             match uu____12208 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____12216,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____12236 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____12259 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____12259
           then
             let uu____12260 =
               let uu____12261 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____12261 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____12260
           else
             (let uu____12265 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____12265))
         in
      let extract_sigelt s =
        (let uu____12277 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____12277
         then
           let uu____12278 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____12278
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____12282 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____12301 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____12318 ->
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
                             (lid,uu____12362,uu____12363,uu____12364,uu____12365,uu____12366)
                             ->
                             ((let uu____12376 =
                                 let uu____12379 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____12379  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____12376);
                              (let uu____12480 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____12480 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____12484,uu____12485,uu____12486,uu____12487,uu____12488)
                             ->
                             ((let uu____12494 =
                                 let uu____12497 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____12497  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____12494);
                              sigelts1)
                         | uu____12598 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____12605 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____12605
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____12611 =
                    let uu___407_12612 = s  in
                    let uu____12613 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___407_12612.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___407_12612.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____12613;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___407_12612.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___407_12612.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____12611])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____12623 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____12623
             then []
             else
               (let uu____12627 = lbs  in
                match uu____12627 with
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
                        (fun uu____12686  ->
                           match uu____12686 with
                           | (uu____12693,t,uu____12695) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____12711  ->
                             match uu____12711 with
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
                           (fun uu____12735  ->
                              match uu____12735 with
                              | (uu____12742,t,uu____12744) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____12752,uu____12753) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____12758 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____12813 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____12813) uu____12758
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____12816 =
                    let uu___408_12817 = s  in
                    let uu____12818 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___408_12817.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___408_12817.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____12818;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___408_12817.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___408_12817.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____12816]
                else [])
             else
               (let uu____12823 =
                  let uu___409_12824 = s  in
                  let uu____12825 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___409_12824.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___409_12824.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____12825;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___409_12824.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___409_12824.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____12823])
         | FStar_Syntax_Syntax.Sig_new_effect uu____12828 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12829 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____12830 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12831 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____12844 -> [s])
         in
      let uu___410_12845 = m  in
      let uu____12846 =
        let uu____12847 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____12847 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___410_12845.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____12846;
        FStar_Syntax_Syntax.exports =
          (uu___410_12845.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int,Prims.int,FStar_TypeChecker_Env.solver_depth_t,Prims.int)
         FStar_Pervasives_Native.tuple4,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____12891  -> FStar_TypeChecker_Env.snapshot env msg)
  
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,FStar_TypeChecker_Env.solver_depth_t,Prims.int)
        FStar_Pervasives_Native.tuple4 FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____12930  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____12943 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____12943
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
  
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
      (let uu____13006 = FStar_Options.debug_any ()  in
       if uu____13006
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
         let uu___411_13011 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___411_13011.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___411_13011.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___411_13011.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___411_13011.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___411_13011.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___411_13011.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___411_13011.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___411_13011.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___411_13011.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___411_13011.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___411_13011.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___411_13011.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___411_13011.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___411_13011.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___411_13011.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___411_13011.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___411_13011.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___411_13011.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___411_13011.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___411_13011.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___411_13011.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___411_13011.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___411_13011.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___411_13011.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___411_13011.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___411_13011.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___411_13011.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___411_13011.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___411_13011.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___411_13011.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___411_13011.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___411_13011.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___411_13011.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___411_13011.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___411_13011.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___411_13011.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___411_13011.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___411_13011.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____13013 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____13013 with
       | (ses,exports,env3) ->
           ((let uu___412_13046 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___412_13046.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___412_13046.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___412_13046.FStar_Syntax_Syntax.is_interface)
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
        let uu____13074 = tc_decls env decls  in
        match uu____13074 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___413_13105 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___413_13105.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___413_13105.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___413_13105.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                     FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple3)
  =
  fun env0  ->
    fun m  ->
      fun iface_exists  ->
        let msg =
          Prims.strcat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let env01 = push_context env0 msg  in
        let uu____13171 = tc_partial_modul env01 m  in
        match uu____13171 with
        | (modul,non_private_decls,env) ->
            finish_partial_modul false iface_exists env modul
              non_private_decls

and (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                         FStar_Pervasives_Native.option,
              FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun loading_from_cache  ->
    fun iface_exists  ->
      fun en  ->
        fun m  ->
          fun exports  ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____13212 = FStar_Errors.get_err_count ()  in
                 uu____13212 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____13223 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____13223
                then
                  let uu____13224 =
                    let uu____13225 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13225 then "" else " (in lax mode) "  in
                  let uu____13227 =
                    let uu____13228 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13228
                    then
                      let uu____13229 =
                        let uu____13230 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____13230 "\n"  in
                      Prims.strcat "\nfrom: " uu____13229
                    else ""  in
                  let uu____13232 =
                    let uu____13233 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13233
                    then
                      let uu____13234 =
                        let uu____13235 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____13235 "\n"  in
                      Prims.strcat "\nto: " uu____13234
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____13224
                    uu____13227 uu____13232
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___414_13241 = en0  in
                    let uu____13242 =
                      let uu____13255 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____13255, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___414_13241.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___414_13241.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___414_13241.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___414_13241.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___414_13241.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___414_13241.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___414_13241.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___414_13241.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___414_13241.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___414_13241.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___414_13241.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___414_13241.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___414_13241.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___414_13241.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___414_13241.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___414_13241.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___414_13241.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___414_13241.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___414_13241.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___414_13241.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___414_13241.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___414_13241.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___414_13241.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___414_13241.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___414_13241.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___414_13241.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___414_13241.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___414_13241.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___414_13241.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___414_13241.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____13242;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___414_13241.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___414_13241.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___414_13241.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___414_13241.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___414_13241.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___414_13241.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___414_13241.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___414_13241.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___414_13241.FStar_TypeChecker_Env.dep_graph)
                    }  in
                  let uu____13292 =
                    let uu____13293 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____13293  in
                  if uu____13292
                  then
                    ((let uu____13295 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____13295 (fun a238  -> ()));
                     z3_reset_options en01)
                  else en01  in
                let uu____13297 = tc_modul en0 modul_iface true  in
                match uu____13297 with
                | (modul_iface1,must_be_none,env) ->
                    if must_be_none <> FStar_Pervasives_Native.None
                    then
                      failwith
                        "Impossible! finish_partial_module: expected the second component to be None"
                    else
                      (((let uu___415_13343 = m  in
                         {
                           FStar_Syntax_Syntax.name =
                             (uu___415_13343.FStar_Syntax_Syntax.name);
                           FStar_Syntax_Syntax.declarations =
                             (uu___415_13343.FStar_Syntax_Syntax.declarations);
                           FStar_Syntax_Syntax.exports =
                             (modul_iface1.FStar_Syntax_Syntax.exports);
                           FStar_Syntax_Syntax.is_interface =
                             (uu___415_13343.FStar_Syntax_Syntax.is_interface)
                         })), (FStar_Pervasives_Native.Some modul_iface1),
                        env)))
            else
              (let modul =
                 let uu____13346 = FStar_Options.use_extracted_interfaces ()
                    in
                 if uu____13346
                 then
                   let uu___416_13347 = m  in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___416_13347.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations =
                       (uu___416_13347.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.exports =
                       (m.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___416_13347.FStar_Syntax_Syntax.is_interface)
                   }
                 else
                   (let uu___417_13349 = m  in
                    {
                      FStar_Syntax_Syntax.name =
                        (uu___417_13349.FStar_Syntax_Syntax.name);
                      FStar_Syntax_Syntax.declarations =
                        (uu___417_13349.FStar_Syntax_Syntax.declarations);
                      FStar_Syntax_Syntax.exports = exports;
                      FStar_Syntax_Syntax.is_interface =
                        (uu___417_13349.FStar_Syntax_Syntax.is_interface)
                    })
                  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____13352 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____13352 FStar_Util.smap_clear);
               (let uu____13380 =
                  ((let uu____13383 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____13383) &&
                     (let uu____13385 =
                        FStar_Options.use_extracted_interfaces ()  in
                      Prims.op_Negation uu____13385))
                    && (Prims.op_Negation loading_from_cache)
                   in
                if uu____13380 then check_exports env modul exports else ());
               (let uu____13388 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____13388 (fun a239  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____13392 =
                  let uu____13393 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____13393  in
                if uu____13392
                then
                  let uu____13394 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____13394 (fun a240  -> ())
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
        let uu____13410 =
          let uu____13411 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____13411  in
        push_context env uu____13410  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____13430 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____13441 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____13441 with | (uu____13450,uu____13451,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                     FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____13481 = FStar_Options.debug_any ()  in
         if uu____13481
         then
           let uu____13482 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____13482
         else ());
        (let env1 =
           let uu___418_13486 = env  in
           let uu____13487 =
             let uu____13488 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____13488  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___418_13486.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___418_13486.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___418_13486.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___418_13486.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___418_13486.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___418_13486.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___418_13486.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___418_13486.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___418_13486.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___418_13486.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___418_13486.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___418_13486.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___418_13486.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___418_13486.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___418_13486.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___418_13486.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___418_13486.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___418_13486.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___418_13486.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____13487;
             FStar_TypeChecker_Env.lax_universes =
               (uu___418_13486.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___418_13486.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___418_13486.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___418_13486.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___418_13486.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___418_13486.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___418_13486.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___418_13486.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___418_13486.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___418_13486.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___418_13486.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___418_13486.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.proof_ns =
               (uu___418_13486.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___418_13486.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___418_13486.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___418_13486.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___418_13486.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___418_13486.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___418_13486.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___418_13486.FStar_TypeChecker_Env.dep_graph)
           }  in
         let uu____13489 = tc_modul env1 m b  in
         match uu____13489 with
         | (m1,m_iface_opt,env2) ->
             ((let uu____13514 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____13514
               then
                 let uu____13515 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____13515
               else ());
              (let uu____13518 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____13518
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.Primops;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                          in
                       let update lb =
                         let uu____13551 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____13551 with
                         | (univnames1,e) ->
                             let uu___419_13558 = lb  in
                             let uu____13559 =
                               let uu____13562 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____13562 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13559;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___419_13558.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___420_13563 = se  in
                       let uu____13564 =
                         let uu____13565 =
                           let uu____13572 =
                             let uu____13573 = FStar_List.map update lbs  in
                             (b1, uu____13573)  in
                           (uu____13572, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____13565  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____13564;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___420_13563.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___420_13563.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___420_13563.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___420_13563.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____13580 -> se  in
                 let normalized_module =
                   let uu___421_13582 = m1  in
                   let uu____13583 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___421_13582.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____13583;
                     FStar_Syntax_Syntax.exports =
                       (uu___421_13582.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___421_13582.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____13584 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____13584
               else ());
              (m1, m_iface_opt, env2)))
  