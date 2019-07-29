open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst in
      let get_n lid =
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero in
      let uu____64 = FStar_Options.reuse_hint_for () in
      match uu____64 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____72 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____72 l in
          let uu___16_73 = env in
          let uu____74 =
            let uu____89 =
              let uu____97 = let uu____103 = get_n lid in (lid, uu____103) in
              FStar_Pervasives_Native.Some uu____97 in
            (tbl, uu____89) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___16_73.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___16_73.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___16_73.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___16_73.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___16_73.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___16_73.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___16_73.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___16_73.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___16_73.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___16_73.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___16_73.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___16_73.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___16_73.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___16_73.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___16_73.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___16_73.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___16_73.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___16_73.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___16_73.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___16_73.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___16_73.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___16_73.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___16_73.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___16_73.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___16_73.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___16_73.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___16_73.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___16_73.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___16_73.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___16_73.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___16_73.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____74;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___16_73.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___16_73.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___16_73.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___16_73.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___16_73.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___16_73.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___16_73.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___16_73.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___16_73.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___16_73.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___16_73.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___16_73.FStar_TypeChecker_Env.strict_args_tab)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____126 = FStar_TypeChecker_Env.current_module env in
                let uu____127 =
                  let uu____129 = FStar_Ident.next_id () in
                  FStar_All.pipe_right uu____129 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____126 uu____127
            | l::uu____134 -> l in
          let uu___25_137 = env in
          let uu____138 =
            let uu____153 =
              let uu____161 = let uu____167 = get_n lid in (lid, uu____167) in
              FStar_Pervasives_Native.Some uu____161 in
            (tbl, uu____153) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___25_137.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___25_137.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___25_137.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___25_137.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___25_137.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___25_137.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___25_137.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___25_137.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___25_137.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___25_137.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___25_137.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___25_137.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___25_137.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___25_137.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___25_137.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___25_137.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___25_137.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___25_137.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___25_137.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___25_137.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___25_137.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___25_137.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___25_137.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___25_137.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___25_137.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___25_137.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___25_137.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___25_137.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___25_137.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___25_137.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___25_137.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____138;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___25_137.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___25_137.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___25_137.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___25_137.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___25_137.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___25_137.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___25_137.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___25_137.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___25_137.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___25_137.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___25_137.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___25_137.FStar_TypeChecker_Env.strict_args_tab)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu____193 =
         let uu____195 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____195 in
       Prims.op_Negation uu____193)
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____212 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____212 with
        | (t1, c, g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun env ->
      fun t ->
        (let uu____242 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____242
         then
           let uu____246 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____246
         else ());
        (let uu____251 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____251 with
         | (t', uu____259, uu____260) ->
             ((let uu____262 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____262
               then
                 let uu____266 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____266
               else ());
              t'))
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____287 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____287
let check_nogen :
  'Auu____297 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____297 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun k ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____320 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1 in
        ([], uu____320)
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env ->
    fun m ->
      fun s ->
        let fail1 uu____356 =
          let uu____357 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____363 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____357 uu____363 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____407)::(wp, uu____409)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____438 -> fail1 ())
        | uu____439 -> fail1 ()
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      let uu____451 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____451 with
      | (open_annotated_univs, annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____483 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____483 t in
          let open_univs_binders n_binders bs =
            let uu____499 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____499 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____509 =
            let uu____516 =
              open_univs_binders Prims.int_zero
                ed.FStar_Syntax_Syntax.binders in
            let uu____518 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____516 uu____518 in
          (match uu____509 with
           | (effect_params_un, signature_un, opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names in
               let uu____523 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un in
               (match uu____523 with
                | (effect_params, env1, uu____532) ->
                    let uu____533 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un in
                    (match uu____533 with
                     | (signature, uu____539) ->
                         let ed1 =
                           let uu___98_541 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___98_541.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___98_541.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___98_541.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___98_541.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___98_541.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___98_541.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___98_541.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___98_541.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___98_541.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___98_541.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___98_541.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___98_541.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___98_541.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___98_541.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___98_541.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([], []) -> ed1
                           | uu____569 ->
                               let op uu____601 =
                                 match uu____601 with
                                 | (us, t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____621 =
                                       let uu____622 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____625 = open_univs n_us t in
                                       FStar_Syntax_Subst.subst uu____622
                                         uu____625 in
                                     (us, uu____621) in
                               let uu___110_628 = ed1 in
                               let uu____629 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____630 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____631 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____632 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____633 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____634 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____635 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____636 =
                                 let uu____637 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____637 in
                               let uu____648 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____649 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____650 =
                                 FStar_List.map
                                   (fun a ->
                                      let uu___113_658 = a in
                                      let uu____659 =
                                        let uu____660 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____660 in
                                      let uu____671 =
                                        let uu____672 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd uu____672 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___113_658.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___113_658.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___113_658.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___113_658.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____659;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____671
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___110_628.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___110_628.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___110_628.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___110_628.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____629;
                                 FStar_Syntax_Syntax.bind_wp = uu____630;
                                 FStar_Syntax_Syntax.if_then_else = uu____631;
                                 FStar_Syntax_Syntax.ite_wp = uu____632;
                                 FStar_Syntax_Syntax.stronger = uu____633;
                                 FStar_Syntax_Syntax.close_wp = uu____634;
                                 FStar_Syntax_Syntax.trivial = uu____635;
                                 FStar_Syntax_Syntax.repr = uu____636;
                                 FStar_Syntax_Syntax.return_repr = uu____648;
                                 FStar_Syntax_Syntax.bind_repr = uu____649;
                                 FStar_Syntax_Syntax.actions = uu____650;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___110_628.FStar_Syntax_Syntax.eff_attrs)
                               } in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____717 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t in
                             let uu____723 = FStar_Ident.range_of_lid mname in
                             FStar_Errors.raise_error uu____717 uu____723 in
                           let uu____730 =
                             let uu____731 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____731.FStar_Syntax_Syntax.n in
                           match uu____730 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a, uu____770)::(wp, uu____772)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____801 -> fail1 signature1)
                           | uu____802 -> fail1 signature1 in
                         let uu____803 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____803 with
                          | (a, wp_a) ->
                              let fresh_effect_signature uu____827 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____834 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un in
                                    (match uu____834 with
                                     | (signature1, uu____846) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____847 ->
                                    let uu____850 =
                                      let uu____855 =
                                        let uu____856 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____856) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____855 in
                                    (match uu____850 with
                                     | (uu____869, signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env2 =
                                let uu____872 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env1 uu____872 in
                              ((let uu____874 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____874
                                then
                                  let uu____879 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____881 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____884 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____886 =
                                    let uu____888 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____888 in
                                  let uu____889 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____879 uu____881 uu____884 uu____886
                                    uu____889
                                else ());
                               (let check_and_gen' env3 uu____924 k =
                                  match uu____924 with
                                  | (us, t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____960::uu____961 ->
                                           let uu____964 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____964 with
                                            | (us1, t1) ->
                                                let uu____987 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____987 with
                                                 | (us2, t2) ->
                                                     let uu____1002 =
                                                       let uu____1003 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2 in
                                                       tc_check_trivial_guard
                                                         uu____1003 t2 k in
                                                     let uu____1004 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____1004)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____1023 =
                                      let uu____1032 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1039 =
                                        let uu____1048 =
                                          let uu____1055 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1055 in
                                        [uu____1048] in
                                      uu____1032 :: uu____1039 in
                                    let uu____1074 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____1023
                                      uu____1074 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____1078 = fresh_effect_signature () in
                                  match uu____1078 with
                                  | (b, wp_b) ->
                                      let a_wp_b =
                                        let uu____1094 =
                                          let uu____1103 =
                                            let uu____1110 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1110 in
                                          [uu____1103] in
                                        let uu____1123 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____1094
                                          uu____1123 in
                                      let expected_k =
                                        let uu____1129 =
                                          let uu____1138 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____1145 =
                                            let uu____1154 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1161 =
                                              let uu____1170 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____1177 =
                                                let uu____1186 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____1193 =
                                                  let uu____1202 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____1202] in
                                                uu____1186 :: uu____1193 in
                                              uu____1170 :: uu____1177 in
                                            uu____1154 :: uu____1161 in
                                          uu____1138 :: uu____1145 in
                                        let uu____1245 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____1129
                                          uu____1245 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____1258 =
                                      let uu____1261 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname in
                                      FStar_Pervasives_Native.Some uu____1261 in
                                    let uu____1262 =
                                      let uu____1263 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____1263
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv uu____1258
                                      uu____1262 in
                                  let expected_k =
                                    let uu____1275 =
                                      let uu____1284 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1291 =
                                        let uu____1300 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____1307 =
                                          let uu____1316 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____1323 =
                                            let uu____1332 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1332] in
                                          uu____1316 :: uu____1323 in
                                        uu____1300 :: uu____1307 in
                                      uu____1284 :: uu____1291 in
                                    let uu____1369 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1275
                                      uu____1369 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1384 =
                                      let uu____1393 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1400 =
                                        let uu____1409 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____1409] in
                                      uu____1393 :: uu____1400 in
                                    let uu____1434 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1384
                                      uu____1434 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____1438 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1438 with
                                  | (t, uu____1444) ->
                                      let expected_k =
                                        let uu____1448 =
                                          let uu____1457 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1464 =
                                            let uu____1473 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____1480 =
                                              let uu____1489 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____1489] in
                                            uu____1473 :: uu____1480 in
                                          uu____1457 :: uu____1464 in
                                        let uu____1520 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____1448
                                          uu____1520 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____1533 =
                                      let uu____1536 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname in
                                      FStar_Pervasives_Native.Some uu____1536 in
                                    let uu____1537 =
                                      let uu____1538 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____1538
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv uu____1533
                                      uu____1537 in
                                  let b_wp_a =
                                    let uu____1550 =
                                      let uu____1559 =
                                        let uu____1566 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1566 in
                                      [uu____1559] in
                                    let uu____1579 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1550
                                      uu____1579 in
                                  let expected_k =
                                    let uu____1585 =
                                      let uu____1594 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1601 =
                                        let uu____1610 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____1617 =
                                          let uu____1626 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____1626] in
                                        uu____1610 :: uu____1617 in
                                      uu____1594 :: uu____1601 in
                                    let uu____1657 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1585
                                      uu____1657 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1661 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1661 with
                                  | (t, uu____1667) ->
                                      let expected_k =
                                        let uu____1671 =
                                          let uu____1680 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1687 =
                                            let uu____1696 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1696] in
                                          uu____1680 :: uu____1687 in
                                        let uu____1721 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1671
                                          uu____1721 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1724 =
                                  let uu____1737 =
                                    let uu____1738 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1738.FStar_Syntax_Syntax.n in
                                  match uu____1737 with
                                  | FStar_Syntax_Syntax.Tm_unknown ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1757 ->
                                      let repr =
                                        let uu____1759 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1759 with
                                        | (t, uu____1765) ->
                                            let expected_k =
                                              let uu____1769 =
                                                let uu____1778 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1785 =
                                                  let uu____1794 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1794] in
                                                uu____1778 :: uu____1785 in
                                              let uu____1819 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1769 uu____1819 in
                                            tc_check_trivial_guard env2
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.EraseUniverses;
                                            FStar_TypeChecker_Env.AllowUnboundUniverses]
                                            env2 repr in
                                        let uu____1836 =
                                          let uu____1843 =
                                            let uu____1844 =
                                              let uu____1861 =
                                                let uu____1872 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1881 =
                                                  let uu____1892 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1892] in
                                                uu____1872 :: uu____1881 in
                                              (repr1, uu____1861) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1844 in
                                          FStar_Syntax_Syntax.mk uu____1843 in
                                        uu____1836
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1950 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1950 wp in
                                      let destruct_repr t =
                                        let uu____1965 =
                                          let uu____1966 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1966.FStar_Syntax_Syntax.n in
                                        match uu____1965 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1977,
                                             (t1, uu____1979)::(wp,
                                                                uu____1981)::[])
                                            -> (t1, wp)
                                        | uu____2040 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____2052 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____2052
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____2053 =
                                          fresh_effect_signature () in
                                        match uu____2053 with
                                        | (b, wp_b) ->
                                            let a_wp_b =
                                              let uu____2069 =
                                                let uu____2078 =
                                                  let uu____2085 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____2085 in
                                                [uu____2078] in
                                              let uu____2098 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____2069 uu____2098 in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b in
                                            let x_a =
                                              let uu____2106 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____2106 in
                                            let wp_g_x =
                                              let uu____2111 =
                                                let uu____2116 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____2117 =
                                                  let uu____2118 =
                                                    let uu____2127 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2127 in
                                                  [uu____2118] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____2116 uu____2117 in
                                              uu____2111
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____2158 =
                                                  let uu____2163 =
                                                    let uu____2164 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____2164
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____2173 =
                                                    let uu____2174 =
                                                      let uu____2177 =
                                                        let uu____2180 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____2181 =
                                                          let uu____2184 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____2185 =
                                                            let uu____2188 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____2189 =
                                                              let uu____2192
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____2192] in
                                                            uu____2188 ::
                                                              uu____2189 in
                                                          uu____2184 ::
                                                            uu____2185 in
                                                        uu____2180 ::
                                                          uu____2181 in
                                                      r :: uu____2177 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2174 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2163 uu____2173 in
                                                uu____2158
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let maybe_range_arg =
                                              let uu____2210 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs in
                                              if uu____2210
                                              then
                                                let uu____2221 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range in
                                                let uu____2228 =
                                                  let uu____2237 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range in
                                                  [uu____2237] in
                                                uu____2221 :: uu____2228
                                              else [] in
                                            let expected_k =
                                              let uu____2273 =
                                                let uu____2282 =
                                                  let uu____2291 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____2298 =
                                                    let uu____2307 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b in
                                                    [uu____2307] in
                                                  uu____2291 :: uu____2298 in
                                                let uu____2332 =
                                                  let uu____2341 =
                                                    let uu____2350 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____2357 =
                                                      let uu____2366 =
                                                        let uu____2373 =
                                                          let uu____2374 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____2374 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____2373 in
                                                      let uu____2375 =
                                                        let uu____2384 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____2391 =
                                                          let uu____2400 =
                                                            let uu____2407 =
                                                              let uu____2408
                                                                =
                                                                let uu____2417
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____2417] in
                                                              let uu____2436
                                                                =
                                                                let uu____2439
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____2439 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____2408
                                                                uu____2436 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2407 in
                                                          [uu____2400] in
                                                        uu____2384 ::
                                                          uu____2391 in
                                                      uu____2366 ::
                                                        uu____2375 in
                                                    uu____2350 :: uu____2357 in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____2341 in
                                                FStar_List.append uu____2282
                                                  uu____2332 in
                                              let uu____2484 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____2273 uu____2484 in
                                            let uu____2487 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k in
                                            (match uu____2487 with
                                             | (expected_k1, uu____2495,
                                                uu____2496) ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env4 =
                                                   let uu___242_2503 = env3 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_sig
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.gamma_sig);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.attrtab
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.attrtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.phase1
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.phase1);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.uvar_subtyping
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.uvar_subtyping);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.fv_delta_depths
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.fv_delta_depths);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.postprocess
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.postprocess);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.nbe
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.nbe);
                                                     FStar_TypeChecker_Env.strict_args_tab
                                                       =
                                                       (uu___242_2503.FStar_TypeChecker_Env.strict_args_tab)
                                                   } in
                                                 let br =
                                                   check_and_gen' env4
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____2516 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____2516 in
                                        let res =
                                          let wp =
                                            let uu____2524 =
                                              let uu____2529 =
                                                let uu____2530 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____2530
                                                  FStar_Pervasives_Native.snd in
                                              let uu____2539 =
                                                let uu____2540 =
                                                  let uu____2543 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____2544 =
                                                    let uu____2547 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____2547] in
                                                  uu____2543 :: uu____2544 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____2540 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____2529 uu____2539 in
                                            uu____2524
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____2559 =
                                            let uu____2568 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____2575 =
                                              let uu____2584 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____2584] in
                                            uu____2568 :: uu____2575 in
                                          let uu____2609 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____2559
                                            uu____2609 in
                                        let uu____2612 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k in
                                        match uu____2612 with
                                        | (expected_k1, uu____2620,
                                           uu____2621) ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____2627 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____2627 with
                                             | (univs1, repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____2650 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos)) in
                                      let actions =
                                        let check_action act =
                                          let uu____2665 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____2679 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs in
                                               match uu____2679 with
                                               | (usubst, uvs) ->
                                                   let uu____2702 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs in
                                                   let uu____2703 =
                                                     let uu___271_2704 = act in
                                                     let uu____2705 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params in
                                                     let uu____2706 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn in
                                                     let uu____2707 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___271_2704.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___271_2704.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____2705;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____2706;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____2707
                                                     } in
                                                   (uu____2702, uu____2703)) in
                                          match uu____2665 with
                                          | (env3, act1) ->
                                              let act_typ =
                                                let uu____2711 =
                                                  let uu____2712 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ in
                                                  uu____2712.FStar_Syntax_Syntax.n in
                                                match uu____2711 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs, c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c in
                                                    let uu____2738 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname in
                                                    if uu____2738
                                                    then
                                                      let uu____2741 =
                                                        let uu____2744 =
                                                          let uu____2745 =
                                                            let uu____2746 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2746 in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____2745 in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____2744 in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____2741
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____2769 ->
                                                    act1.FStar_Syntax_Syntax.action_typ in
                                              let uu____2770 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ in
                                              (match uu____2770 with
                                               | (act_typ1, uu____2778, g_t)
                                                   ->
                                                   let env' =
                                                     let uu___288_2781 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1 in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___288_2781.FStar_TypeChecker_Env.strict_args_tab)
                                                     } in
                                                   ((let uu____2784 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED") in
                                                     if uu____2784
                                                     then
                                                       let uu____2788 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name in
                                                       let uu____2790 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn in
                                                       let uu____2792 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1 in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____2788
                                                         uu____2790
                                                         uu____2792
                                                     else ());
                                                    (let uu____2797 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn in
                                                     match uu____2797 with
                                                     | (act_defn, uu____2805,
                                                        g_a) ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant]
                                                             env3 act_defn in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant;
                                                             FStar_TypeChecker_Env.Eager_unfolding;
                                                             FStar_TypeChecker_Env.Beta]
                                                             env3 act_typ1 in
                                                         let uu____2809 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2 in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs, c) ->
                                                               let uu____2845
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c in
                                                               (match uu____2845
                                                                with
                                                                | (bs1,
                                                                   uu____2857)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____2864
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2864 in
                                                                    let uu____2867
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k in
                                                                    (match uu____2867
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____2881,
                                                                    g) ->
                                                                    (k1, g)))
                                                           | uu____2885 ->
                                                               let uu____2886
                                                                 =
                                                                 let uu____2892
                                                                   =
                                                                   let uu____2894
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                   let uu____2896
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____2894
                                                                    uu____2896 in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____2892) in
                                                               FStar_Errors.raise_error
                                                                 uu____2886
                                                                 act_defn1.FStar_Syntax_Syntax.pos in
                                                         (match uu____2809
                                                          with
                                                          | (expected_k, g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k in
                                                              ((let uu____2914
                                                                  =
                                                                  let uu____2915
                                                                    =
                                                                    let uu____2916
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____2916 in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____2915 in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____2914);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____2918
                                                                    =
                                                                    let uu____2919
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____2919.FStar_Syntax_Syntax.n in
                                                                  match uu____2918
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs, c)
                                                                    ->
                                                                    let uu____2944
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                    (match uu____2944
                                                                    with
                                                                    | 
                                                                    (bs1, c1)
                                                                    ->
                                                                    let uu____2951
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____2951
                                                                    with
                                                                    | 
                                                                    (a1, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2972
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1 in
                                                                    [uu____2972] in
                                                                    let uu____2973
                                                                    =
                                                                    let uu____2984
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____2984] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2971;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2973;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____3009
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3009))
                                                                  | uu____3012
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                let uu____3014
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
                                                                    let uu____3036
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____3036)) in
                                                                match uu____3014
                                                                with
                                                                | (univs1,
                                                                   act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env3
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4 in
                                                                    let uu___338_3055
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___338_3055.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___338_3055.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___338_3055.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))) in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action) in
                                      (repr, bind_repr, return_repr, actions) in
                                match uu____1724 with
                                | (repr, bind_repr, return_repr, actions) ->
                                    let t0 =
                                      let uu____3079 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____3079 in
                                    let uu____3082 =
                                      let uu____3087 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____3087 with
                                      | (gen_univs, t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____3106 ->
                                               let uu____3109 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____3116 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____3116 =
                                                             Prims.int_zero)
                                                      gen_univs
                                                      annotated_univ_names) in
                                               if uu____3109
                                               then (gen_univs, t)
                                               else
                                                 (let uu____3127 =
                                                    let uu____3133 =
                                                      let uu____3135 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names) in
                                                      let uu____3137 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs) in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____3135 uu____3137 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____3133) in
                                                  FStar_Errors.raise_error
                                                    uu____3127
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                    (match uu____3082 with
                                     | (univs1, t) ->
                                         let signature1 =
                                           let uu____3148 =
                                             let uu____3161 =
                                               let uu____3162 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____3162.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____3161) in
                                           match uu____3148 with
                                           | ([], uu____3173) -> t
                                           | (uu____3188,
                                              FStar_Syntax_Syntax.Tm_arrow
                                              (uu____3189, c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____3227 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____3255 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____3255 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____3262 =
                                              ((n1 >= Prims.int_zero) &&
                                                 (let uu____3266 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____3266))
                                                && (m <> n1) in
                                            if uu____3262
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____3284 =
                                                  FStar_Util.string_of_int m in
                                                let uu____3286 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____3288 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____3284 uu____3286
                                                  uu____3288 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____3304 =
                                             close1 (~- Prims.int_one)
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____3304 with
                                           | (univs2, defn) ->
                                               let uu____3320 =
                                                 close1 (~- Prims.int_one)
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____3320 with
                                                | (univs', typ) ->
                                                    let uu___388_3337 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___388_3337.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___388_3337.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___388_3337.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___391_3340 = ed2 in
                                           let uu____3341 =
                                             close1 Prims.int_zero return_wp in
                                           let uu____3343 =
                                             close1 Prims.int_one bind_wp in
                                           let uu____3345 =
                                             close1 Prims.int_zero
                                               if_then_else1 in
                                           let uu____3347 =
                                             close1 Prims.int_zero ite_wp in
                                           let uu____3349 =
                                             close1 Prims.int_zero stronger in
                                           let uu____3351 =
                                             close1 Prims.int_one close_wp in
                                           let uu____3353 =
                                             close1 Prims.int_zero trivial_wp in
                                           let uu____3355 =
                                             let uu____3356 =
                                               close1 Prims.int_zero
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____3356 in
                                           let uu____3374 =
                                             close1 Prims.int_zero
                                               return_repr in
                                           let uu____3376 =
                                             close1 Prims.int_one bind_repr in
                                           let uu____3378 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___391_3340.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___391_3340.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____3341;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____3343;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____3345;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____3347;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____3349;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____3351;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____3353;
                                             FStar_Syntax_Syntax.repr =
                                               uu____3355;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____3374;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____3376;
                                             FStar_Syntax_Syntax.actions =
                                               uu____3378;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___391_3340.FStar_Syntax_Syntax.eff_attrs)
                                           } in
                                         ((let uu____3382 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____3382
                                           then
                                             let uu____3387 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____3387
                                           else ());
                                          ed3))))))))
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env ->
    fun ed ->
      let uu____3413 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____3413 with
      | (effect_binders_un, signature_un) ->
          let uu____3430 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____3430 with
           | (effect_binders, env1, uu____3449) ->
               let uu____3450 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____3450 with
                | (signature, uu____3466) ->
                    let raise_error1 uu____3482 =
                      match uu____3482 with
                      | (e, err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3518 ->
                           match uu____3518 with
                           | (bv, qual) ->
                               let uu____3537 =
                                 let uu___416_3538 = bv in
                                 let uu____3539 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___416_3538.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___416_3538.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3539
                                 } in
                               (uu____3537, qual)) effect_binders in
                    let uu____3544 =
                      let uu____3551 =
                        let uu____3552 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____3552.FStar_Syntax_Syntax.n in
                      match uu____3551 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a, uu____3562)::[], effect_marker) ->
                          (a, effect_marker)
                      | uu____3594 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature") in
                    (match uu____3544 with
                     | (a, effect_marker) ->
                         let a1 =
                           let uu____3620 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____3620
                           then
                             let uu____3623 =
                               let uu____3626 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____3626 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3623
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____3674 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____3674 with
                           | (t2, comp, uu____3687) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____3696 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____3696 with
                          | (repr, _comp) ->
                              ((let uu____3720 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____3720
                                then
                                  let uu____3724 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3724
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let uu____3731 =
                                  recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____3734 =
                                    let uu____3735 =
                                      let uu____3736 =
                                        let uu____3753 =
                                          let uu____3764 =
                                            let uu____3773 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____3776 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____3773, uu____3776) in
                                          [uu____3764] in
                                        (wp_type, uu____3753) in
                                      FStar_Syntax_Syntax.Tm_app uu____3736 in
                                    mk1 uu____3735 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____3734 in
                                let effect_signature =
                                  let binders =
                                    let uu____3824 =
                                      let uu____3831 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____3831) in
                                    let uu____3837 =
                                      let uu____3846 =
                                        let uu____3853 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____3853
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____3846] in
                                    uu____3824 :: uu____3837 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let uu____3890 =
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
                                  let uu____3956 = item in
                                  match uu____3956 with
                                  | (u_item, item1) ->
                                      let uu____3971 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____3971 with
                                       | (item2, item_comp) ->
                                           ((let uu____3987 =
                                               let uu____3989 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____3989 in
                                             if uu____3987
                                             then
                                               let uu____3992 =
                                                 let uu____3998 =
                                                   let uu____4000 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____4002 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____4000 uu____4002 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____3998) in
                                               FStar_Errors.raise_err
                                                 uu____3992
                                             else ());
                                            (let uu____4008 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____4008 with
                                             | (item_t, item_wp, item_elab)
                                                 ->
                                                 let uu____4026 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let uu____4028 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____4030 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____4030 with
                                | (dmff_env1, uu____4056, bind_wp, bind_elab)
                                    ->
                                    let uu____4059 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____4059 with
                                     | (dmff_env2, uu____4085, return_wp,
                                        return_elab) ->
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
                                           let uu____4094 =
                                             let uu____4095 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____4095.FStar_Syntax_Syntax.n in
                                           match uu____4094 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____4153 =
                                                 let uu____4172 =
                                                   let uu____4177 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____4177 in
                                                 match uu____4172 with
                                                 | (b11::b21::[], body1) ->
                                                     (b11, b21, body1)
                                                 | uu____4259 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____4153 with
                                                | (b11, b21, body1) ->
                                                    let env0 =
                                                      let uu____4313 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4313 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4336 =
                                                          let uu____4337 =
                                                            let uu____4354 =
                                                              let uu____4365
                                                                =
                                                                let uu____4374
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____4379
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____4374,
                                                                  uu____4379) in
                                                              [uu____4365] in
                                                            (wp_type,
                                                              uu____4354) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4337 in
                                                        mk1 uu____4336 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____4415 =
                                                      let uu____4424 =
                                                        let uu____4425 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4425 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4424 in
                                                    (match uu____4415 with
                                                     | (bs1, body2, what') ->
                                                         let fail1 uu____4448
                                                           =
                                                           let error_msg =
                                                             let uu____4451 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____4453 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____4451
                                                               uu____4453 in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg) in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                               -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____4463
                                                                   =
                                                                   let uu____4465
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                                   Prims.op_Negation
                                                                    uu____4465 in
                                                                 if
                                                                   uu____4463
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4470
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
                                                                    fail1 ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____4470
                                                                   (fun a1 ->
                                                                    ()))));
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
                                                             let uu____4499 =
                                                               let uu____4504
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____4505
                                                                 =
                                                                 let uu____4506
                                                                   =
                                                                   let uu____4515
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____4515,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____4506] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4504
                                                                 uu____4505 in
                                                             uu____4499
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____4550 =
                                                             let uu____4551 =
                                                               let uu____4560
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____4560] in
                                                             b11 ::
                                                               uu____4551 in
                                                           let uu____4585 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____4550
                                                             uu____4585
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4588 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let return_wp1 =
                                           let uu____4596 =
                                             let uu____4597 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____4597.FStar_Syntax_Syntax.n in
                                           match uu____4596 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____4655 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4655
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4676 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let bind_wp1 =
                                           let uu____4684 =
                                             let uu____4685 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____4685.FStar_Syntax_Syntax.n in
                                           match uu____4684 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders, body, what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None in
                                               let uu____4719 =
                                                 let uu____4720 =
                                                   let uu____4729 =
                                                     let uu____4736 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4736 in
                                                   [uu____4729] in
                                                 FStar_List.append uu____4720
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____4719 body what
                                           | uu____4755 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind") in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu____4785 =
                                                let uu____4786 =
                                                  let uu____4787 =
                                                    let uu____4804 =
                                                      let uu____4815 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4815 in
                                                    (t, uu____4804) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4787 in
                                                mk1 uu____4786 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4785) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4873 = f a2 in
                                               [uu____4873]
                                           | x::xs ->
                                               let uu____4884 =
                                                 apply_last1 f xs in
                                               x :: uu____4884 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____4918 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____4918 with
                                           | FStar_Pervasives_Native.Some
                                               (_us, _t) ->
                                               ((let uu____4948 =
                                                   FStar_Options.debug_any () in
                                                 if uu____4948
                                                 then
                                                   let uu____4951 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____4951
                                                 else ());
                                                (let uu____4956 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____4956))
                                           | FStar_Pervasives_Native.None ->
                                               let uu____4965 =
                                                 let uu____4970 = mk_lid name in
                                                 let uu____4971 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____4970 uu____4971 in
                                               (match uu____4965 with
                                                | (sigelt, fv) ->
                                                    ((let uu____4975 =
                                                        let uu____4978 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____4978 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____4975);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____5032 =
                                             let uu____5035 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true"))) in
                                             let uu____5038 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____5035 :: uu____5038 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____5032);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____5090 =
                                              let uu____5093 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions) in
                                              let uu____5094 =
                                                FStar_ST.op_Bang sigelts in
                                              uu____5093 :: uu____5094 in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____5090);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____5146 =
                                               let uu____5149 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true"))) in
                                               let uu____5152 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____5149 :: uu____5152 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____5146);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____5204 =
                                                let uu____5207 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions) in
                                                let uu____5208 =
                                                  FStar_ST.op_Bang sigelts in
                                                uu____5207 :: uu____5208 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____5204);
                                             (let uu____5257 =
                                                FStar_List.fold_left
                                                  (fun uu____5297 ->
                                                     fun action ->
                                                       match uu____5297 with
                                                       | (dmff_env3, actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____5318 =
                                                             let uu____5325 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____5325
                                                               params_un in
                                                           (match uu____5318
                                                            with
                                                            | (action_params,
                                                               env',
                                                               uu____5334) ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____5360
                                                                    ->
                                                                    match uu____5360
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    qual) ->
                                                                    let uu____5379
                                                                    =
                                                                    let uu___609_5380
                                                                    = bv in
                                                                    let uu____5381
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___609_5380.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___609_5380.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____5381
                                                                    } in
                                                                    (uu____5379,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____5387
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____5387
                                                                 with
                                                                 | (dmff_env4,
                                                                    action_t,
                                                                    action_wp,
                                                                    action_elab)
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
                                                                    uu____5426
                                                                    ->
                                                                    let uu____5427
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5427 in
                                                                    ((
                                                                    let uu____5431
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____5431
                                                                    then
                                                                    let uu____5436
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____5439
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____5442
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____5444
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5436
                                                                    uu____5439
                                                                    uu____5442
                                                                    uu____5444
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____5453
                                                                    =
                                                                    let uu____5456
                                                                    =
                                                                    let uu___631_5457
                                                                    = action in
                                                                    let uu____5458
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____5459
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___631_5457.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___631_5457.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___631_5457.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5458;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5459
                                                                    } in
                                                                    uu____5456
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____5453))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____5257 with
                                              | (dmff_env3, actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____5503 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____5510 =
                                                        let uu____5519 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____5519] in
                                                      uu____5503 ::
                                                        uu____5510 in
                                                    let uu____5544 =
                                                      let uu____5547 =
                                                        let uu____5548 =
                                                          let uu____5549 =
                                                            let uu____5566 =
                                                              let uu____5577
                                                                =
                                                                let uu____5586
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____5589
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____5586,
                                                                  uu____5589) in
                                                              [uu____5577] in
                                                            (repr,
                                                              uu____5566) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5549 in
                                                        mk1 uu____5548 in
                                                      let uu____5625 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____5547
                                                        uu____5625 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____5544
                                                      FStar_Pervasives_Native.None in
                                                  let uu____5626 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr2 =
                                                    register "repr" repr1 in
                                                  let uu____5630 =
                                                    let uu____5639 =
                                                      let uu____5640 =
                                                        let uu____5643 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____5643 in
                                                      uu____5640.FStar_Syntax_Syntax.n in
                                                    match uu____5639 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,
                                                         arrow1, uu____5657)
                                                        ->
                                                        let uu____5694 =
                                                          let uu____5715 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____5715
                                                          with
                                                          | (b::bs, body) ->
                                                              (b, bs, body)
                                                          | uu____5783 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____5694
                                                         with
                                                         | (type_param1,
                                                            effect_param1,
                                                            arrow2) ->
                                                             let uu____5848 =
                                                               let uu____5849
                                                                 =
                                                                 let uu____5852
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5852 in
                                                               uu____5849.FStar_Syntax_Syntax.n in
                                                             (match uu____5848
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,
                                                                   c)
                                                                  ->
                                                                  let uu____5885
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____5885
                                                                   with
                                                                   | 
                                                                   (wp_binders1,
                                                                    c1) ->
                                                                    let uu____5900
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5931
                                                                    ->
                                                                    match uu____5931
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    uu____5940)
                                                                    ->
                                                                    let uu____5945
                                                                    =
                                                                    let uu____5947
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____5947
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____5945
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____5900
                                                                    with
                                                                    | 
                                                                    (pre_args,
                                                                    post_args)
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
                                                                    let uu____6039
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____6039 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____6049
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6060
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____6060 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____6070
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____6073
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____6070,
                                                                    uu____6073)))
                                                              | uu____6088 ->
                                                                  let uu____6089
                                                                    =
                                                                    let uu____6095
                                                                    =
                                                                    let uu____6097
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____6097 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____6095) in
                                                                  raise_error1
                                                                    uu____6089))
                                                    | uu____6109 ->
                                                        let uu____6110 =
                                                          let uu____6116 =
                                                            let uu____6118 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____6118 in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____6116) in
                                                        raise_error1
                                                          uu____6110 in
                                                  (match uu____5630 with
                                                   | (pre, post) ->
                                                       ((let uu____6151 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____6154 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____6157 =
                                                           register "wp"
                                                             wp_type in
                                                         ());
                                                        (let ed1 =
                                                           let uu___687_6160
                                                             = ed in
                                                           let uu____6161 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____6162 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature in
                                                           let uu____6163 =
                                                             let uu____6164 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____6164) in
                                                           let uu____6171 =
                                                             let uu____6172 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____6172) in
                                                           let uu____6179 =
                                                             apply_close
                                                               repr2 in
                                                           let uu____6180 =
                                                             let uu____6181 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____6181) in
                                                           let uu____6188 =
                                                             let uu____6189 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____6189) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____6161;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____6162;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____6163;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____6171;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____6179;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____6180;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____6188;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___687_6160.FStar_Syntax_Syntax.eff_attrs)
                                                           } in
                                                         let uu____6196 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____6196
                                                         with
                                                         | (sigelts', ed2) ->
                                                             ((let uu____6214
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____6214
                                                               then
                                                                 let uu____6218
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____6218
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    Prims.int_zero
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____6238
                                                                    =
                                                                    let uu____6241
                                                                    =
                                                                    let uu____6242
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____6242) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6241 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____6238;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____6249
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____6249
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____6252
                                                                 =
                                                                 let uu____6255
                                                                   =
                                                                   let uu____6258
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____6258 in
                                                                 FStar_List.append
                                                                   uu____6255
                                                                   sigelts' in
                                                               (uu____6252,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t :
  'Auu____6299 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6299 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let err_range =
            let uu____6334 = FStar_List.hd ses in
            uu____6334.FStar_Syntax_Syntax.sigrng in
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
           | uu____6339 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1, uu____6345, [], t, uu____6347, uu____6348);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6350;
               FStar_Syntax_Syntax.sigattrs = uu____6351;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,
                                                                  uu____6353,
                                                                  _t_top,
                                                                  _lex_t_top,
                                                                  _6387,
                                                                  uu____6356);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6358;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6359;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons, uu____6361, _t_cons, _lex_t_cons, _6395,
                    uu____6364);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6366;
                 FStar_Syntax_Syntax.sigattrs = uu____6367;_}::[]
               when
               ((_6387 = Prims.int_zero) && (_6395 = Prims.int_zero)) &&
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
                 let uu____6420 =
                   let uu____6427 =
                     let uu____6428 =
                       let uu____6435 =
                         let uu____6438 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1 in
                         FStar_Syntax_Syntax.fvar uu____6438
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____6435, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____6428 in
                   FStar_Syntax_Syntax.mk uu____6427 in
                 uu____6420 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
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
                   let uu____6453 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6453 in
                 let hd1 =
                   let uu____6455 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6455 in
                 let tl1 =
                   let uu____6457 =
                     let uu____6458 =
                       let uu____6465 =
                         let uu____6466 =
                           let uu____6473 =
                             let uu____6476 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2 in
                             FStar_Syntax_Syntax.fvar uu____6476
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____6473, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____6466 in
                       FStar_Syntax_Syntax.mk uu____6465 in
                     uu____6458 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6457 in
                 let res =
                   let uu____6482 =
                     let uu____6489 =
                       let uu____6490 =
                         let uu____6497 =
                           let uu____6500 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2 in
                           FStar_Syntax_Syntax.fvar uu____6500
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____6497,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____6490 in
                     FStar_Syntax_Syntax.mk uu____6489 in
                   uu____6482 FStar_Pervasives_Native.None r2 in
                 let uu____6503 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6503 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let uu____6542 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6542;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6547 ->
               let err_msg =
                 let uu____6552 =
                   let uu____6554 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____6554 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6552 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun uu____6579 ->
      fun expected_typ1 ->
        fun r ->
          match uu____6579 with
          | (uvs, t) ->
              let uu____6592 = FStar_Syntax_Subst.open_univ_vars uvs t in
              (match uu____6592 with
               | (uvs1, t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1 in
                   if uvs1 = []
                   then
                     let uu____6604 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2 in
                     (match uu____6604 with
                      | (uvs2, t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6622 =
                        let uu____6625 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1) in
                        FStar_All.pipe_right uu____6625
                          (FStar_Syntax_Subst.close_univ_vars uvs1) in
                      (uvs1, uu____6622)))
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____6648 =
          let uu____6649 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____6649 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____6648 r
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____6674 =
          let uu____6675 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____6675 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____6674 r
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          (let uu____6724 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
           if uu____6724
           then
             let uu____6727 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6727
           else ());
          (let uu____6732 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids in
           match uu____6732 with
           | (sig_bndle, tcs, datas) ->
               let data_ops_ses =
                 let uu____6763 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas in
                 FStar_All.pipe_right uu____6763 FStar_List.flatten in
               ((let uu____6777 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6780 =
                        FStar_TypeChecker_Env.should_verify env in
                      Prims.op_Negation uu____6780) in
                 if uu____6777
                 then ()
                 else
                   (let env1 =
                      FStar_TypeChecker_Env.push_sigelt env sig_bndle in
                    FStar_List.iter
                      (fun ty ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env1 in
                         if Prims.op_Negation b
                         then
                           let uu____6796 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid, uu____6806, uu____6807, uu____6808,
                                  uu____6809, uu____6810)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6819 -> failwith "Impossible!" in
                           match uu____6796 with
                           | (lid, r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d ->
                         let uu____6838 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid, uu____6848, uu____6849, ty_lid,
                                uu____6851, uu____6852)
                               -> (data_lid, ty_lid)
                           | uu____6859 -> failwith "Impossible" in
                         match uu____6838 with
                         | (data_lid, ty_lid) ->
                             let uu____6867 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____6870 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1 in
                                  Prims.op_Negation uu____6870) in
                             if uu____6867
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____6884 =
                   let lid =
                     let ty = FStar_List.hd tcs in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid, uu____6889, uu____6890, uu____6891,
                          uu____6892, uu____6893)
                         -> lid
                     | uu____6902 -> failwith "Impossible" in
                   FStar_List.existsb
                     (fun s -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                     FStar_TypeChecker_TcInductive.early_prims_inductives in
                 let is_noeq =
                   FStar_List.existsb (fun q -> q = FStar_Syntax_Syntax.Noeq)
                     quals in
                 let res =
                   let uu____6920 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq in
                   if uu____6920
                   then (sig_bndle, data_ops_ses)
                   else
                     (let is_unopteq =
                        FStar_List.existsb
                          (fun q -> q = FStar_Syntax_Syntax.Unopteq) quals in
                      let ses1 =
                        if is_unopteq
                        then
                          FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                            sig_bndle tcs datas env
                        else
                          FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                            sig_bndle tcs datas env in
                      (sig_bndle, (FStar_List.append ses1 data_ops_ses))) in
                 res)))
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let pop1 uu____6995 =
            let uu____6996 = FStar_TypeChecker_Env.pop env1 "tc_inductive" in
            () in
          try
            (fun uu___865_7006 ->
               match () with
               | () ->
                   let uu____7013 = tc_inductive' env1 ses quals lids in
                   FStar_All.pipe_right uu____7013 (fun r -> pop1 (); r)) ()
          with | uu___864_7044 -> (pop1 (); FStar_Exn.raise uu___864_7044)
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun se ->
    let comb f1 f2 =
      match (f1, f2) with
      | (FStar_Pervasives_Native.Some (e1, l1), FStar_Pervasives_Native.Some
         (e2, l2)) ->
          FStar_Pervasives_Native.Some
            ((FStar_List.append e1 e2), (l1 || l2))
      | (FStar_Pervasives_Native.Some (e, l), FStar_Pervasives_Native.None)
          -> FStar_Pervasives_Native.Some (e, l)
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (e, l))
          -> FStar_Pervasives_Native.Some (e, l)
      | uu____7360 -> FStar_Pervasives_Native.None in
    FStar_List.fold_right
      (fun at ->
         fun acc ->
           let uu____7418 = FStar_ToSyntax_ToSyntax.get_fail_attr true at in
           comb uu____7418 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
let list_of_option :
  'Auu____7443 .
    'Auu____7443 FStar_Pervasives_Native.option -> 'Auu____7443 Prims.list
  =
  fun uu___0_7452 ->
    match uu___0_7452 with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some x -> [x]
let (check_multi_eq :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1 ->
    fun l2 ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____7532 = collect1 tl1 in
            (match uu____7532 with
             | [] -> [(hd1, Prims.int_one)]
             | (h, n1)::t ->
                 if h = hd1
                 then (h, (n1 + Prims.int_one)) :: t
                 else (hd1, Prims.int_one) :: (h, n1) :: t) in
      let summ l = collect1 l in
      let l11 = summ l1 in
      let l21 = summ l2 in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], []) -> FStar_Pervasives_Native.None
        | ((e, n1)::uu____7770, []) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([], (e, n1)::uu____7826) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n1)
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2 in
      aux l11 l21
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
          let uu____8036 =
            let uu____8038 = FStar_Options.ide () in
            Prims.op_Negation uu____8038 in
          if uu____8036
          then
            let uu____8041 =
              let uu____8046 = FStar_TypeChecker_Env.dsenv env in
              let uu____8047 = FStar_TypeChecker_Env.current_module env in
              FStar_Syntax_DsEnv.iface_decls uu____8046 uu____8047 in
            (match uu____8041 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some iface_decls1 ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                         let has_iface_val =
                           FStar_All.pipe_right iface_decls1
                             (FStar_Util.for_some
                                (FStar_Parser_AST.decl_is_val
                                   ((lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident)) in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu____8080 =
                                FStar_Syntax_Syntax.range_of_fv lbname in
                              let uu____8081 =
                                let uu____8087 =
                                  let uu____8089 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  let uu____8091 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8089 uu____8091 in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8087) in
                              FStar_Errors.log_issue uu____8080 uu____8081
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8098 =
                                   FStar_Syntax_Syntax.range_of_fv lbname in
                                 let uu____8099 =
                                   let uu____8105 =
                                     let uu____8107 =
                                       FStar_Syntax_Print.fv_to_string lbname in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8107 in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8105) in
                                 FStar_Errors.log_issue uu____8098 uu____8099)
                              else ())
                         else ())))
          else ()
      | uu____8117 -> ()
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun se ->
      let env = env0 in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8162 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8190 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses, lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_bundle (ses, lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           let ses1 =
             let uu____8250 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1) in
             if uu____8250
             then
               let ses1 =
                 let uu____8258 =
                   let uu____8259 =
                     let uu____8260 =
                       tc_inductive
                         (let uu___997_8269 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___997_8269.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___997_8269.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___997_8269.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___997_8269.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___997_8269.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___997_8269.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___997_8269.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___997_8269.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___997_8269.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___997_8269.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___997_8269.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___997_8269.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___997_8269.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___997_8269.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___997_8269.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___997_8269.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___997_8269.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___997_8269.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___997_8269.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___997_8269.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___997_8269.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___997_8269.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___997_8269.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___997_8269.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___997_8269.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___997_8269.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___997_8269.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___997_8269.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___997_8269.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___997_8269.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___997_8269.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___997_8269.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___997_8269.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___997_8269.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___997_8269.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___997_8269.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___997_8269.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___997_8269.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___997_8269.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___997_8269.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___997_8269.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___997_8269.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids in
                     FStar_All.pipe_right uu____8260
                       FStar_Pervasives_Native.fst in
                   FStar_All.pipe_right uu____8259
                     (FStar_TypeChecker_Normalize.elim_uvars env1) in
                 FStar_All.pipe_right uu____8258
                   FStar_Syntax_Util.ses_of_sigbundle in
               ((let uu____8283 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases") in
                 if uu____8283
                 then
                   let uu____8288 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1001_8292 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1001_8292.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1001_8292.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1001_8292.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1001_8292.FStar_Syntax_Syntax.sigattrs)
                        }) in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8288
                 else ());
                ses1)
             else ses in
           let uu____8302 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____8302 with
            | (sigbndle, projectors_ses) ->
                let sigbndle1 =
                  let uu___1008_8326 = sigbndle in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1008_8326.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1008_8326.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1008_8326.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1008_8326.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  } in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____8338 = cps_and_elaborate env ne in
           (match uu____8338 with
            | (ses, ne1, lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1022_8377 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1022_8377.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1022_8377.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1022_8377.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1022_8377.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None ->
                      [(let uu___1025_8379 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1025_8379.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1025_8379.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1025_8379.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1025_8379.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____8386 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env) in
             if uu____8386
             then
               let ne1 =
                 let uu____8390 =
                   let uu____8391 =
                     let uu____8392 =
                       tc_eff_decl
                         (let uu___1031_8395 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1031_8395.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1031_8395.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1031_8395.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1031_8395.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1031_8395.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1031_8395.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1031_8395.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1031_8395.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1031_8395.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1031_8395.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1031_8395.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1031_8395.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1031_8395.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1031_8395.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1031_8395.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1031_8395.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1031_8395.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1031_8395.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1031_8395.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1031_8395.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1031_8395.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1031_8395.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1031_8395.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1031_8395.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1031_8395.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1031_8395.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1031_8395.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1031_8395.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1031_8395.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1031_8395.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1031_8395.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1031_8395.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1031_8395.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1031_8395.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1031_8395.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1031_8395.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1031_8395.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1031_8395.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1031_8395.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1031_8395.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1031_8395.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1031_8395.FStar_TypeChecker_Env.strict_args_tab)
                          }) ne in
                     FStar_All.pipe_right uu____8392
                       (fun ne1 ->
                          let uu___1034_8401 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1034_8401.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1034_8401.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1034_8401.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1034_8401.FStar_Syntax_Syntax.sigattrs)
                          }) in
                   FStar_All.pipe_right uu____8391
                     (FStar_TypeChecker_Normalize.elim_uvars env) in
                 FStar_All.pipe_right uu____8390
                   FStar_Syntax_Util.eff_decl_of_new_effect in
               ((let uu____8403 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases") in
                 if uu____8403
                 then
                   let uu____8408 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1038_8412 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1038_8412.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1038_8412.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1038_8412.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1038_8412.FStar_Syntax_Syntax.sigattrs)
                        }) in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____8408
                 else ());
                ne1)
             else ne in
           let ne2 = tc_eff_decl env ne1 in
           let se1 =
             let uu___1043_8420 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___1043_8420.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___1043_8420.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___1043_8420.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___1043_8420.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target in
           let uu____8428 =
             let uu____8435 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8435 in
           (match uu____8428 with
            | (a, wp_a_src) ->
                let uu____8452 =
                  let uu____8459 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8459 in
                (match uu____8452 with
                 | (b, wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8477 =
                         let uu____8480 =
                           let uu____8481 =
                             let uu____8488 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____8488) in
                           FStar_Syntax_Syntax.NT uu____8481 in
                         [uu____8480] in
                       FStar_Syntax_Subst.subst uu____8477 wp_b_tgt in
                     let expected_k =
                       let uu____8496 =
                         let uu____8505 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____8512 =
                           let uu____8521 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____8521] in
                         uu____8505 :: uu____8512 in
                       let uu____8546 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____8496 uu____8546 in
                     let repr_type eff_name a1 wp =
                       (let uu____8568 =
                          let uu____8570 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name in
                          Prims.op_Negation uu____8570 in
                        if uu____8568
                        then
                          let uu____8573 =
                            let uu____8579 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____8579) in
                          let uu____8583 =
                            FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error uu____8573 uu____8583
                        else ());
                       (let uu____8586 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                        match uu____8586 with
                        | FStar_Pervasives_Native.None ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr)) in
                            let uu____8623 =
                              FStar_TypeChecker_Env.get_range env in
                            let uu____8624 =
                              let uu____8631 =
                                let uu____8632 =
                                  let uu____8649 =
                                    let uu____8660 =
                                      FStar_Syntax_Syntax.as_arg a1 in
                                    let uu____8669 =
                                      let uu____8680 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____8680] in
                                    uu____8660 :: uu____8669 in
                                  (repr, uu____8649) in
                                FStar_Syntax_Syntax.Tm_app uu____8632 in
                              FStar_Syntax_Syntax.mk uu____8631 in
                            uu____8624 FStar_Pervasives_Native.None
                              uu____8623) in
                     let uu____8725 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None) ->
                           failwith "Impossible (parser)"
                       | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                           ->
                           let uu____8898 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____8909 =
                                 FStar_Syntax_Subst.univ_var_opening uvs in
                               match uu____8909 with
                               | (usubst, uvs1) ->
                                   let uu____8932 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1 in
                                   let uu____8933 =
                                     FStar_Syntax_Subst.subst usubst lift_wp in
                                   (uu____8932, uu____8933)
                             else (env, lift_wp) in
                           (match uu____8898 with
                            | (env1, lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k in
                                     let uu____8983 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2 in
                                     (uvs, uu____8983)) in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some (what, lift),
                          FStar_Pervasives_Native.None) ->
                           let uu____9054 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____9069 =
                                 FStar_Syntax_Subst.univ_var_opening what in
                               match uu____9069 with
                               | (usubst, uvs) ->
                                   let uu____9094 =
                                     FStar_Syntax_Subst.subst usubst lift in
                                   (uvs, uu____9094)
                             else ([], lift) in
                           (match uu____9054 with
                            | (uvs, lift1) ->
                                ((let uu____9130 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED") in
                                  if uu____9130
                                  then
                                    let uu____9134 =
                                      FStar_Syntax_Print.term_to_string lift1 in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9134
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange) in
                                  let uu____9140 =
                                    let uu____9147 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9147 lift1 in
                                  match uu____9140 with
                                  | (lift2, comp, uu____9172) ->
                                      let uu____9173 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2 in
                                      (match uu____9173 with
                                       | (uu____9202, lift_wp, lift_elab) ->
                                           let lift_wp1 =
                                             recheck_debug "lift-wp" env
                                               lift_wp in
                                           let lift_elab1 =
                                             recheck_debug "lift-elab" env
                                               lift_elab in
                                           if
                                             (FStar_List.length uvs) =
                                               Prims.int_zero
                                           then
                                             let uu____9234 =
                                               let uu____9245 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1 in
                                               FStar_Pervasives_Native.Some
                                                 uu____9245 in
                                             let uu____9262 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1 in
                                             (uu____9234, uu____9262)
                                           else
                                             (let uu____9291 =
                                                let uu____9302 =
                                                  let uu____9311 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1 in
                                                  (uvs, uu____9311) in
                                                FStar_Pervasives_Native.Some
                                                  uu____9302 in
                                              let uu____9326 =
                                                let uu____9335 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1 in
                                                (uvs, uu____9335) in
                                              (uu____9291, uu____9326)))))) in
                     (match uu____8725 with
                      | (lift, lift_wp) ->
                          let env1 =
                            let uu___1119_9409 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1119_9409.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1119_9409.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1119_9409.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1119_9409.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1119_9409.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1119_9409.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1119_9409.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1119_9409.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1119_9409.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1119_9409.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1119_9409.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1119_9409.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1119_9409.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1119_9409.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1119_9409.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1119_9409.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1119_9409.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1119_9409.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1119_9409.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1119_9409.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1119_9409.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1119_9409.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1119_9409.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1119_9409.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1119_9409.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1119_9409.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1119_9409.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1119_9409.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1119_9409.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1119_9409.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1119_9409.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1119_9409.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1119_9409.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1119_9409.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1119_9409.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1119_9409.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1119_9409.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1119_9409.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1119_9409.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1119_9409.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1119_9409.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1119_9409.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1119_9409.FStar_TypeChecker_Env.strict_args_tab)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs, lift1) ->
                                let uu____9466 =
                                  let uu____9471 =
                                    FStar_Syntax_Subst.univ_var_opening uvs in
                                  match uu____9471 with
                                  | (usubst, uvs1) ->
                                      let uu____9494 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1 in
                                      let uu____9495 =
                                        FStar_Syntax_Subst.subst usubst lift1 in
                                      (uu____9494, uu____9495) in
                                (match uu____9466 with
                                 | (env2, lift2) ->
                                     let uu____9508 =
                                       let uu____9515 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9515 in
                                     (match uu____9508 with
                                      | (a1, wp_a_src1) ->
                                          let wp_a =
                                            FStar_Syntax_Syntax.new_bv
                                              FStar_Pervasives_Native.None
                                              wp_a_src1 in
                                          let a_typ =
                                            FStar_Syntax_Syntax.bv_to_name a1 in
                                          let wp_a_typ =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_a in
                                          let repr_f =
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.source
                                              a_typ wp_a_typ in
                                          let repr_result =
                                            let lift_wp1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp) in
                                            let lift_wp_a =
                                              let uu____9549 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              let uu____9550 =
                                                let uu____9557 =
                                                  let uu____9558 =
                                                    let uu____9575 =
                                                      let uu____9586 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ in
                                                      let uu____9595 =
                                                        let uu____9606 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ in
                                                        [uu____9606] in
                                                      uu____9586 ::
                                                        uu____9595 in
                                                    (lift_wp1, uu____9575) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9558 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9557 in
                                              uu____9550
                                                FStar_Pervasives_Native.None
                                                uu____9549 in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a in
                                          let expected_k1 =
                                            let uu____9654 =
                                              let uu____9663 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1 in
                                              let uu____9670 =
                                                let uu____9679 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a in
                                                let uu____9686 =
                                                  let uu____9695 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f in
                                                  [uu____9695] in
                                                uu____9679 :: uu____9686 in
                                              uu____9663 :: uu____9670 in
                                            let uu____9726 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result in
                                            FStar_Syntax_Util.arrow
                                              uu____9654 uu____9726 in
                                          let uu____9729 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1 in
                                          (match uu____9729 with
                                           | (expected_k2, uu____9747,
                                              uu____9748) ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     Prims.int_zero
                                                 then
                                                   check_and_gen env2 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env2 lift2
                                                        expected_k2 in
                                                    let uu____9772 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3 in
                                                    (uvs, uu____9772)) in
                                               FStar_Pervasives_Native.Some
                                                 lift3))) in
                          ((let uu____9788 =
                              let uu____9790 =
                                let uu____9792 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst in
                                FStar_All.pipe_right uu____9792
                                  FStar_List.length in
                              uu____9790 <> Prims.int_one in
                            if uu____9788
                            then
                              let uu____9814 =
                                let uu____9820 =
                                  let uu____9822 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source in
                                  let uu____9824 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target in
                                  let uu____9826 =
                                    let uu____9828 =
                                      let uu____9830 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____9830
                                        FStar_List.length in
                                    FStar_All.pipe_right uu____9828
                                      FStar_Util.string_of_int in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9822 uu____9824 uu____9826 in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9820) in
                              FStar_Errors.raise_error uu____9814 r
                            else ());
                           (let uu____9857 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____9868 =
                                   let uu____9870 =
                                     let uu____9873 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must in
                                     FStar_All.pipe_right uu____9873
                                       FStar_Pervasives_Native.fst in
                                   FStar_All.pipe_right uu____9870
                                     FStar_List.length in
                                 uu____9868 <> Prims.int_one) in
                            if uu____9857
                            then
                              let uu____9927 =
                                let uu____9933 =
                                  let uu____9935 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source in
                                  let uu____9937 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target in
                                  let uu____9939 =
                                    let uu____9941 =
                                      let uu____9943 =
                                        let uu____9946 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must in
                                        FStar_All.pipe_right uu____9946
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____9943
                                        FStar_List.length in
                                    FStar_All.pipe_right uu____9941
                                      FStar_Util.string_of_int in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9935 uu____9937 uu____9939 in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9933) in
                              FStar_Errors.raise_error uu____9927 r
                            else ());
                           (let sub2 =
                              let uu___1156_10005 = sub1 in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1156_10005.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1156_10005.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              } in
                            let se1 =
                              let uu___1159_10007 = se in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1159_10007.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1159_10007.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1159_10007.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1159_10007.FStar_Syntax_Syntax.sigattrs)
                              } in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags) ->
           let uu____10021 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____10049 = FStar_Syntax_Subst.univ_var_opening uvs in
                match uu____10049 with
                | (usubst, uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                    let c1 =
                      let uu____10080 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst in
                      FStar_Syntax_Subst.subst_comp uu____10080 c in
                    let uu____10089 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                    (uu____10089, uvs1, tps1, c1)) in
           (match uu____10021 with
            | (env1, uvs1, tps1, c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r in
                let uu____10111 = FStar_Syntax_Subst.open_comp tps1 c1 in
                (match uu____10111 with
                 | (tps2, c2) ->
                     let uu____10128 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                     (match uu____10128 with
                      | (tps3, env3, us) ->
                          let uu____10148 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                          (match uu____10148 with
                           | (c3, u, g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x, uu____10176)::uu____10177 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10196 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3 in
                                 let uu____10204 =
                                   let uu____10206 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ in
                                   Prims.op_Negation uu____10206 in
                                 if uu____10204
                                 then
                                   let uu____10209 =
                                     let uu____10215 =
                                       let uu____10217 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ in
                                       let uu____10219 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10217 uu____10219 in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10215) in
                                   FStar_Errors.raise_error uu____10209 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3 in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3 in
                                 let uu____10227 =
                                   let uu____10228 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10228 in
                                 match uu____10227 with
                                 | (uvs2, t) ->
                                     let uu____10259 =
                                       let uu____10264 =
                                         let uu____10277 =
                                           let uu____10278 =
                                             FStar_Syntax_Subst.compress t in
                                           uu____10278.FStar_Syntax_Syntax.n in
                                         (tps4, uu____10277) in
                                       match uu____10264 with
                                       | ([], FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10293, c5)) -> ([], c5)
                                       | (uu____10335,
                                          FStar_Syntax_Syntax.Tm_arrow
                                          (tps5, c5)) -> (tps5, c5)
                                       | uu____10374 ->
                                           failwith
                                             "Impossible (t is an arrow)" in
                                     (match uu____10259 with
                                      | (tps5, c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____10408 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t in
                                              match uu____10408 with
                                              | (uu____10413, t1) ->
                                                  let uu____10415 =
                                                    let uu____10421 =
                                                      let uu____10423 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid in
                                                      let uu____10425 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int in
                                                      let uu____10429 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1 in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10423
                                                        uu____10425
                                                        uu____10429 in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10421) in
                                                  FStar_Errors.raise_error
                                                    uu____10415 r)
                                           else ();
                                           (let se1 =
                                              let uu___1229_10436 = se in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1229_10436.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1229_10436.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1229_10436.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1229_10436.FStar_Syntax_Syntax.sigattrs)
                                              } in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10443, uu____10444, uu____10445) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10450 ->
                   match uu___1_10450 with
                   | FStar_Syntax_Syntax.OnlyName -> true
                   | uu____10453 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10459, uu____10460) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10469 ->
                   match uu___1_10469 with
                   | FStar_Syntax_Syntax.OnlyName -> true
                   | uu____10472 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           ((let uu____10483 = FStar_TypeChecker_Env.lid_exists env1 lid in
             if uu____10483
             then
               let uu____10486 =
                 let uu____10492 =
                   let uu____10494 = FStar_Ident.text_of_lid lid in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10494 in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10492) in
               FStar_Errors.raise_error uu____10486 r
             else ());
            (let uu____10500 =
               let uu____10509 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1) in
               if uu____10509
               then
                 let uu____10520 =
                   tc_declare_typ
                     (let uu___1253_10523 = env1 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1253_10523.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1253_10523.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1253_10523.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1253_10523.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1253_10523.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1253_10523.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1253_10523.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1253_10523.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1253_10523.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1253_10523.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1253_10523.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1253_10523.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1253_10523.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1253_10523.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1253_10523.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1253_10523.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1253_10523.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1253_10523.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1253_10523.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1253_10523.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1253_10523.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1253_10523.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1253_10523.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1253_10523.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1253_10523.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1253_10523.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1253_10523.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1253_10523.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1253_10523.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1253_10523.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1253_10523.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1253_10523.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1253_10523.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1253_10523.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1253_10523.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1253_10523.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1253_10523.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1253_10523.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1253_10523.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1253_10523.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1253_10523.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1253_10523.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1253_10523.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng in
                 match uu____10520 with
                 | (uvs1, t1) ->
                     ((let uu____10548 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases") in
                       if uu____10548
                       then
                         let uu____10553 =
                           FStar_Syntax_Print.term_to_string t1 in
                         let uu____10555 =
                           FStar_Syntax_Print.univ_names_to_string uvs1 in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10553 uu____10555
                       else ());
                      (uvs1, t1))
               else (uvs, t) in
             match uu____10500 with
             | (uvs1, t1) ->
                 let uu____10590 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng in
                 (match uu____10590 with
                  | (uvs2, t2) ->
                      ([(let uu___1266_10620 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1266_10620.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1266_10620.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1266_10620.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1266_10620.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           let uu____10625 =
             let uu____10634 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1) in
             if uu____10634
             then
               let uu____10645 =
                 tc_assume
                   (let uu___1275_10648 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1275_10648.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1275_10648.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1275_10648.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1275_10648.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1275_10648.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1275_10648.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1275_10648.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1275_10648.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1275_10648.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1275_10648.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1275_10648.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1275_10648.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1275_10648.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1275_10648.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1275_10648.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1275_10648.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1275_10648.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1275_10648.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1275_10648.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1275_10648.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1275_10648.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1275_10648.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1275_10648.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1275_10648.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1275_10648.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1275_10648.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1275_10648.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1275_10648.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1275_10648.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1275_10648.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1275_10648.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1275_10648.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1275_10648.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1275_10648.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1275_10648.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1275_10648.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1275_10648.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1275_10648.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1275_10648.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1275_10648.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1275_10648.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1275_10648.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng in
               match uu____10645 with
               | (uvs1, t1) ->
                   ((let uu____10674 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____10674
                     then
                       let uu____10679 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10681 =
                         FStar_Syntax_Print.univ_names_to_string uvs1 in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____10679
                         uu____10681
                     else ());
                    (uvs1, t1))
             else (uvs, t) in
           (match uu____10625 with
            | (uvs1, t1) ->
                let uu____10716 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng in
                (match uu____10716 with
                 | (uvs2, t2) ->
                     ([(let uu___1288_10746 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1288_10746.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1288_10746.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1288_10746.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1288_10746.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit in
           let uu____10750 = FStar_TypeChecker_TcTerm.tc_term env2 e in
           (match uu____10750 with
            | (e1, c, g1) ->
                let uu____10770 =
                  let uu____10777 =
                    let uu____10780 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____10780 in
                  let uu____10781 =
                    let uu____10786 = FStar_Syntax_Syntax.lcomp_comp c in
                    (e1, uu____10786) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____10777 uu____10781 in
                (match uu____10770 with
                 | (e2, uu____10798, g) ->
                     ((let uu____10801 =
                         FStar_TypeChecker_Env.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____10801);
                      (let se1 =
                         let uu___1303_10803 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1303_10803.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1303_10803.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1303_10803.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1303_10803.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
           ((let uu____10815 = FStar_Options.debug_any () in
             if uu____10815
             then
               let uu____10818 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule in
               let uu____10820 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____10818
                 uu____10820
             else ());
            (let uu____10825 = FStar_TypeChecker_TcTerm.tc_tactic env t in
             match uu____10825 with
             | (t1, uu____10843, g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1 in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses in
                   FStar_List.iter
                     (fun lid ->
                        let uu____10857 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids' in
                        match uu____10857 with
                        | FStar_Pervasives_Native.None when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____10860 =
                              let uu____10866 =
                                let uu____10868 =
                                  FStar_Ident.string_of_lid lid in
                                let uu____10870 =
                                  let uu____10872 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids' in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____10872 in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____10868 uu____10870 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____10866) in
                            FStar_Errors.raise_error uu____10860 r
                        | uu____10884 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses in
                    let env1 =
                      let uu___1324_10889 = env in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1324_10889.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1324_10889.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1324_10889.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1324_10889.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1324_10889.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1324_10889.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1324_10889.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1324_10889.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1324_10889.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1324_10889.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1324_10889.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1324_10889.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1324_10889.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1324_10889.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1324_10889.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1324_10889.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1324_10889.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1324_10889.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1324_10889.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1324_10889.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1324_10889.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1324_10889.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1324_10889.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1324_10889.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1324_10889.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1324_10889.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1324_10889.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1324_10889.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1324_10889.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1324_10889.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1324_10889.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1324_10889.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1324_10889.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1324_10889.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1324_10889.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1324_10889.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1324_10889.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1324_10889.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1324_10889.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1324_10889.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1324_10889.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1324_10889.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1324_10889.FStar_TypeChecker_Env.strict_args_tab)
                      } in
                    ([], ses, env1))))))
       | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r in
           let check_quals_eq l qopt val_q =
             match qopt with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some val_q
             | FStar_Pervasives_Native.Some q' ->
                 let drop_logic =
                   FStar_List.filter
                     (fun x ->
                        Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)) in
                 let uu____10957 =
                   let uu____10959 =
                     let uu____10968 = drop_logic val_q in
                     let uu____10971 = drop_logic q' in
                     (uu____10968, uu____10971) in
                   match uu____10959 with
                   | (val_q1, q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                 if uu____10957
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____10998 =
                      let uu____11004 =
                        let uu____11006 = FStar_Syntax_Print.lid_to_string l in
                        let uu____11008 =
                          FStar_Syntax_Print.quals_to_string val_q in
                        let uu____11010 =
                          FStar_Syntax_Print.quals_to_string q' in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11006 uu____11008 uu____11010 in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11004) in
                    FStar_Errors.raise_error uu____10998 r) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____11047 =
                   let uu____11048 = FStar_Syntax_Subst.compress def in
                   uu____11048.FStar_Syntax_Syntax.n in
                 match uu____11047 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders, uu____11060, uu____11061) -> binders
                 | uu____11086 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs, c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11098;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([], uu____11203) -> val_bs1
                     | (uu____11234, []) -> val_bs1
                     | ((body_bv, uu____11266)::bt, (val_bv, aqual)::vt) ->
                         let uu____11323 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true, uu____11347) -> (val_bv, aqual)
                           | (false, true) ->
                               ((let uu___1393_11361 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1395_11364 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1395_11364.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1393_11361.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1393_11361.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false, false) -> (val_bv, aqual))) ::
                           uu____11323 in
                   let uu____11371 =
                     let uu____11378 =
                       let uu____11379 =
                         let uu____11394 = rename_binders1 def_bs val_bs in
                         (uu____11394, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____11379 in
                     FStar_Syntax_Syntax.mk uu____11378 in
                   uu____11371 FStar_Pervasives_Native.None r1
               | uu____11413 -> typ1 in
             let uu___1401_11414 = lb in
             let uu____11415 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11415;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1401_11414.FStar_Syntax_Syntax.lbpos)
             } in
           let uu____11418 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11473 ->
                     fun lb ->
                       match uu____11473 with
                       | (gen1, lbs1, quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____11519 =
                             let uu____11531 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____11531 with
                             | FStar_Pervasives_Native.None ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs, tval), quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____11611 ->
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
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____11658 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos)) in
                                   (false, uu____11658, quals_opt1))) in
                           (match uu____11519 with
                            | (gen2, lb1, quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____11418 with
            | (should_generalize, lbs', quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____11762 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_11768 ->
                                match uu___2_11768 with
                                | FStar_Syntax_Syntax.Irreducible -> true
                                | FStar_Syntax_Syntax.Visible_default -> true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____11773 -> false)) in
                      if uu____11762
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____11786 =
                    let uu____11793 =
                      let uu____11794 =
                        let uu____11808 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____11808) in
                      FStar_Syntax_Syntax.Tm_let uu____11794 in
                    FStar_Syntax_Syntax.mk uu____11793 in
                  uu____11786 FStar_Pervasives_Native.None r in
                let env' =
                  let uu___1444_11827 = env1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1444_11827.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1444_11827.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1444_11827.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1444_11827.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1444_11827.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1444_11827.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1444_11827.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1444_11827.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1444_11827.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1444_11827.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1444_11827.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1444_11827.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1444_11827.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1444_11827.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1444_11827.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1444_11827.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1444_11827.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1444_11827.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1444_11827.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1444_11827.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1444_11827.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1444_11827.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1444_11827.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1444_11827.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1444_11827.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1444_11827.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1444_11827.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1444_11827.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1444_11827.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1444_11827.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1444_11827.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1444_11827.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1444_11827.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1444_11827.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1444_11827.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1444_11827.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1444_11827.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1444_11827.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1444_11827.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1444_11827.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1444_11827.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1444_11827.FStar_TypeChecker_Env.strict_args_tab)
                  } in
                let e1 =
                  let uu____11830 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env') in
                  if uu____11830
                  then
                    let drop_lbtyp e_lax =
                      let uu____11839 =
                        let uu____11840 = FStar_Syntax_Subst.compress e_lax in
                        uu____11840.FStar_Syntax_Syntax.n in
                      match uu____11839 with
                      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
                          let lb_unannotated =
                            let uu____11862 =
                              let uu____11863 = FStar_Syntax_Subst.compress e in
                              uu____11863.FStar_Syntax_Syntax.n in
                            match uu____11862 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____11867, lb1::[]), uu____11869) ->
                                let uu____11885 =
                                  let uu____11886 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp in
                                  uu____11886.FStar_Syntax_Syntax.n in
                                (match uu____11885 with
                                 | FStar_Syntax_Syntax.Tm_unknown -> true
                                 | uu____11891 -> false)
                            | uu____11893 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!" in
                          if lb_unannotated
                          then
                            let uu___1469_11897 = e_lax in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1471_11912 = lb in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1471_11912.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1469_11897.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1469_11897.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____11915 -> e_lax in
                    let uu____11916 =
                      FStar_Util.record_time
                        (fun uu____11924 ->
                           let uu____11925 =
                             let uu____11926 =
                               let uu____11927 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1475_11936 = env' in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1475_11936.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1475_11936.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1475_11936.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1475_11936.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1475_11936.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1475_11936.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1475_11936.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1475_11936.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1475_11936.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1475_11936.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1475_11936.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1475_11936.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1475_11936.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1475_11936.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1475_11936.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1475_11936.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1475_11936.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1475_11936.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1475_11936.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1475_11936.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1475_11936.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1475_11936.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1475_11936.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1475_11936.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1475_11936.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1475_11936.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1475_11936.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1475_11936.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1475_11936.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1475_11936.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1475_11936.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1475_11936.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1475_11936.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1475_11936.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1475_11936.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1475_11936.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1475_11936.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1475_11936.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1475_11936.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1475_11936.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1475_11936.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1475_11936.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e in
                               FStar_All.pipe_right uu____11927
                                 (fun uu____11949 ->
                                    match uu____11949 with
                                    | (e1, uu____11957, uu____11958) -> e1) in
                             FStar_All.pipe_right uu____11926
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env') in
                           FStar_All.pipe_right uu____11925 drop_lbtyp) in
                    match uu____11916 with
                    | (e1, ms) ->
                        ((let uu____11964 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases") in
                          if uu____11964
                          then
                            let uu____11969 =
                              FStar_Syntax_Print.term_to_string e1 in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____11969
                          else ());
                         (let uu____11975 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime") in
                          if uu____11975
                          then
                            let uu____11980 = FStar_Util.string_of_int ms in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____11980
                          else ());
                         e1)
                  else e in
                let uu____11987 =
                  let uu____11996 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs in
                  match uu____11996 with
                  | FStar_Pervasives_Native.None ->
                      ((se.FStar_Syntax_Syntax.sigattrs),
                        FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats, (tau, FStar_Pervasives_Native.None)::[]) ->
                      (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats, args) ->
                      (FStar_Errors.log_issue r
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_with`");
                       ((se.FStar_Syntax_Syntax.sigattrs),
                         FStar_Pervasives_Native.None)) in
                (match uu____11987 with
                 | (attrs, post_tau) ->
                     let se1 =
                       let uu___1505_12101 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1505_12101.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1505_12101.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1505_12101.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1505_12101.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       } in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef in
                       let uu___1512_12114 = lb in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1512_12114.FStar_Syntax_Syntax.lbpos)
                       } in
                     let uu____12115 =
                       FStar_Util.record_time
                         (fun uu____12134 ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1) in
                     (match uu____12115 with
                      | (r1, ms) ->
                          ((let uu____12162 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime") in
                            if uu____12162
                            then
                              let uu____12167 = FStar_Util.string_of_int ms in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____12167
                            else ());
                           (let uu____12172 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1, e2);
                                   FStar_Syntax_Syntax.pos = uu____12197;
                                   FStar_Syntax_Syntax.vars = uu____12198;_},
                                 uu____12199, g) when
                                  FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____12229 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters) in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____12229) in
                                  let lbs3 =
                                    let uu____12253 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.snd lbs2 in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____12253) in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____12276,
                                         FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____12281 -> quals in
                                  ((let uu___1542_12290 = se1 in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1542_12290.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1542_12290.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1542_12290.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____12293 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)" in
                            match uu____12172 with
                            | (se2, lbs1) ->
                                (FStar_All.pipe_right
                                   (FStar_Pervasives_Native.snd lbs1)
                                   (FStar_List.iter
                                      (fun lb ->
                                         let fv =
                                           FStar_Util.right
                                             lb.FStar_Syntax_Syntax.lbname in
                                         FStar_TypeChecker_Env.insert_fv_info
                                           env1 fv
                                           lb.FStar_Syntax_Syntax.lbtyp));
                                 (let uu____12349 = log env1 in
                                  if uu____12349
                                  then
                                    let uu____12352 =
                                      let uu____12354 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb ->
                                                let should_log =
                                                  let uu____12374 =
                                                    let uu____12383 =
                                                      let uu____12384 =
                                                        let uu____12387 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname in
                                                        uu____12387.FStar_Syntax_Syntax.fv_name in
                                                      uu____12384.FStar_Syntax_Syntax.v in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____12383 in
                                                  match uu____12374 with
                                                  | FStar_Pervasives_Native.None
                                                      -> true
                                                  | uu____12396 -> false in
                                                if should_log
                                                then
                                                  let uu____12408 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname in
                                                  let uu____12410 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____12408
                                                    uu____12410
                                                else "")) in
                                      FStar_All.pipe_right uu____12354
                                        (FStar_String.concat "\n") in
                                    FStar_Util.print1 "%s\n" uu____12352
                                  else ());
                                 check_must_erase_attribute env0 se2;
                                 ([se2], [], env0))))))))
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun se ->
      let env1 = set_hint_correlator env se in
      (let uu____12462 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____12462
       then
         let uu____12465 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12465
       else ());
      (let uu____12470 = get_fail_se se in
       match uu____12470 with
       | FStar_Pervasives_Native.Some (uu____12491, false) when
           let uu____12508 = FStar_TypeChecker_Env.should_verify env1 in
           Prims.op_Negation uu____12508 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos, lax1) ->
           let env' =
             if lax1
             then
               let uu___1573_12534 = env1 in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1573_12534.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1573_12534.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1573_12534.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1573_12534.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1573_12534.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1573_12534.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1573_12534.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1573_12534.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1573_12534.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1573_12534.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1573_12534.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1573_12534.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1573_12534.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1573_12534.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1573_12534.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1573_12534.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1573_12534.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1573_12534.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1573_12534.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1573_12534.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1573_12534.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1573_12534.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1573_12534.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1573_12534.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1573_12534.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1573_12534.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1573_12534.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1573_12534.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1573_12534.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1573_12534.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1573_12534.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1573_12534.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1573_12534.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1573_12534.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1573_12534.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1573_12534.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1573_12534.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1573_12534.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1573_12534.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1573_12534.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1573_12534.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1573_12534.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1573_12534.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1 in
           ((let uu____12539 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____12539
             then
               let uu____12542 =
                 let uu____12544 =
                   FStar_List.map FStar_Util.string_of_int errnos in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12544 in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12542
             else ());
            (let uu____12558 =
               FStar_Errors.catch_errors
                 (fun uu____12588 ->
                    FStar_Options.with_saved_options
                      (fun uu____12600 -> tc_decl' env' se)) in
             match uu____12558 with
             | (errs, uu____12612) ->
                 ((let uu____12642 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                   if uu____12642
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x -> fun y -> x - y) in
                   let errnos1 = sort errnos in
                   let actual =
                     let uu____12677 =
                       FStar_List.concatMap
                         (fun i -> list_of_option i.FStar_Errors.issue_number)
                         errs in
                     sort uu____12677 in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12689 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12700 =
                            let uu____12710 = check_multi_eq errnos1 actual in
                            match uu____12710 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one)) in
                          (match uu____12700 with
                           | (e, n1, n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____12775 =
                                   let uu____12781 =
                                     let uu____12783 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1 in
                                     let uu____12786 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual in
                                     let uu____12789 =
                                       FStar_Util.string_of_int e in
                                     let uu____12791 =
                                       FStar_Util.string_of_int n2 in
                                     let uu____12793 =
                                       FStar_Util.string_of_int n1 in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____12783 uu____12786 uu____12789
                                       uu____12791 uu____12793 in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____12781) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12775)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None -> tc_decl' env1 se)
let for_export :
  'Auu____12820 .
    'Auu____12820 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env ->
    fun hidden ->
      fun se ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___3_12863 ->
                  match uu___3_12863 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | uu____12866 -> false)) in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l, uu____12877) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____12885 -> false in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____12895 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____12900 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____12916 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____12942 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____12968) ->
            let uu____12977 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____12977
            then
              let for_export_bundle se1 uu____13014 =
                match uu____13014 with
                | (out, hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, us, bs, t, uu____13053, uu____13054) ->
                         let dec =
                           let uu___1649_13064 = se1 in
                           let uu____13065 =
                             let uu____13066 =
                               let uu____13073 =
                                 let uu____13074 =
                                   FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow bs uu____13074 in
                               (l, us, uu____13073) in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13066 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13065;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1649_13064.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1649_13064.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1649_13064.FStar_Syntax_Syntax.sigattrs)
                           } in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l, us, t, uu____13084, uu____13085, uu____13086) ->
                         let dec =
                           let uu___1660_13094 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1660_13094.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1660_13094.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1660_13094.FStar_Syntax_Syntax.sigattrs)
                           } in
                         ((dec :: out), (l :: hidden1))
                     | uu____13099 -> (out, hidden1)) in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13122, uu____13123, uu____13124) ->
            let uu____13125 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____13125 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
            let uu____13149 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc) in
            if uu____13149
            then
              ([(let uu___1676_13168 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1676_13168.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1676_13168.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1676_13168.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13171 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_13177 ->
                         match uu___4_13177 with
                         | FStar_Syntax_Syntax.Assumption -> true
                         | FStar_Syntax_Syntax.Projector uu____13180 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13186 ->
                             true
                         | uu____13188 -> false)) in
               if uu____13171 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13209 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13214 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13219 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13224 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13229 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____13247) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____13261 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
            if uu____13261
            then ([], hidden)
            else
              (let dec =
                 let uu____13282 = FStar_Ident.range_of_lid lid in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13282;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
            let uu____13293 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____13293
            then
              let uu____13304 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb ->
                        let uu___1713_13318 = se in
                        let uu____13319 =
                          let uu____13320 =
                            let uu____13327 =
                              let uu____13328 =
                                let uu____13331 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname in
                                uu____13331.FStar_Syntax_Syntax.fv_name in
                              uu____13328.FStar_Syntax_Syntax.v in
                            (uu____13327, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp)) in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13320 in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13319;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1713_13318.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1713_13318.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1713_13318.FStar_Syntax_Syntax.sigattrs)
                        })) in
              (uu____13304, hidden)
            else ([se], hidden)
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      (let uu____13354 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____13354
       then
         let uu____13357 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13357
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13362 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13380 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____13397) ->
           let env1 =
             let uu___1734_13402 = env in
             let uu____13403 = FStar_Options.using_facts_from () in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1734_13402.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1734_13402.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1734_13402.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1734_13402.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1734_13402.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1734_13402.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1734_13402.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1734_13402.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1734_13402.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1734_13402.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1734_13402.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1734_13402.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1734_13402.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1734_13402.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1734_13402.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1734_13402.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1734_13402.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1734_13402.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1734_13402.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1734_13402.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1734_13402.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1734_13402.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1734_13402.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1734_13402.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1734_13402.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1734_13402.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1734_13402.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1734_13402.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1734_13402.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1734_13402.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1734_13402.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1734_13402.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1734_13402.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1734_13402.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13403;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1734_13402.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1734_13402.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1734_13402.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1734_13402.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1734_13402.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1734_13402.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1734_13402.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1734_13402.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1734_13402.FStar_TypeChecker_Env.strict_args_tab)
             } in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions) ->
           let env1 =
             let uu___1734_13405 = env in
             let uu____13406 = FStar_Options.using_facts_from () in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1734_13405.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1734_13405.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1734_13405.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1734_13405.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1734_13405.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1734_13405.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1734_13405.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1734_13405.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1734_13405.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1734_13405.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1734_13405.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1734_13405.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1734_13405.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1734_13405.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1734_13405.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1734_13405.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1734_13405.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1734_13405.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1734_13405.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1734_13405.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1734_13405.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1734_13405.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1734_13405.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1734_13405.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1734_13405.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1734_13405.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1734_13405.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1734_13405.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1734_13405.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1734_13405.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1734_13405.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1734_13405.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1734_13405.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1734_13405.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13406;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1734_13405.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1734_13405.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1734_13405.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1734_13405.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1734_13405.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1734_13405.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1734_13405.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1734_13405.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1734_13405.FStar_TypeChecker_Env.strict_args_tab)
             } in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____13407) ->
           let env1 =
             let uu___1734_13410 = env in
             let uu____13411 = FStar_Options.using_facts_from () in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1734_13410.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1734_13410.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1734_13410.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1734_13410.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1734_13410.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1734_13410.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1734_13410.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1734_13410.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1734_13410.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1734_13410.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1734_13410.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1734_13410.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1734_13410.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1734_13410.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1734_13410.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1734_13410.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1734_13410.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1734_13410.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1734_13410.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1734_13410.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1734_13410.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1734_13410.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1734_13410.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1734_13410.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1734_13410.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1734_13410.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1734_13410.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1734_13410.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1734_13410.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1734_13410.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1734_13410.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1734_13410.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1734_13410.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1734_13410.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13411;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1734_13410.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1734_13410.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1734_13410.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1734_13410.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1734_13410.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1734_13410.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1734_13410.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1734_13410.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1734_13410.FStar_TypeChecker_Env.strict_args_tab)
             } in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13412) ->
           let env1 =
             let uu___1734_13417 = env in
             let uu____13418 = FStar_Options.using_facts_from () in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1734_13417.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1734_13417.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1734_13417.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1734_13417.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1734_13417.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1734_13417.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1734_13417.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1734_13417.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1734_13417.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1734_13417.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1734_13417.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1734_13417.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1734_13417.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1734_13417.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1734_13417.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1734_13417.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1734_13417.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1734_13417.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1734_13417.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1734_13417.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1734_13417.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1734_13417.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1734_13417.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1734_13417.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1734_13417.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1734_13417.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1734_13417.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1734_13417.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1734_13417.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1734_13417.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1734_13417.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1734_13417.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1734_13417.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1734_13417.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13418;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1734_13417.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1734_13417.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1734_13417.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1734_13417.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1734_13417.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1734_13417.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1734_13417.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1734_13417.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1734_13417.FStar_TypeChecker_Env.strict_args_tab)
             } in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver)
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____13420 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13421 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2 ->
                   fun a ->
                     let uu____13431 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13431) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13432, uu____13433, uu____13434) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13439 ->
                   match uu___5_13439 with
                   | FStar_Syntax_Syntax.OnlyName -> true
                   | uu____13442 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13444, uu____13445) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13454 ->
                   match uu___5_13454 with
                   | FStar_Syntax_Syntax.OnlyName -> true
                   | uu____13457 -> false))
           -> env
       | uu____13459 -> FStar_TypeChecker_Env.push_sigelt env se)
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____13528 se =
        match uu____13528 with
        | (ses1, exports, env1, hidden) ->
            ((let uu____13581 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____13581
              then
                let uu____13584 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13584
              else ());
             (let uu____13589 = tc_decl env1 se in
              match uu____13589 with
              | (ses', ses_elaborated, env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1 ->
                            (let uu____13642 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF") in
                             if uu____13642
                             then
                               let uu____13646 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13646
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1 ->
                            (let uu____13662 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF") in
                             if uu____13662
                             then
                               let uu____13666 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13666
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                  (FStar_TypeChecker_Env.promote_id_info env2
                     (fun t ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.AllowUnboundUniverses;
                          FStar_TypeChecker_Env.CheckNoUvars;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                          FStar_TypeChecker_Env.CompressUvars;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Zeta;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Iota;
                          FStar_TypeChecker_Env.NoFullNorm] env2 t);
                   (let env3 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env3 -> fun se1 -> add_sigelt_to_env env3 se1)
                           env2) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____13683 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____13683
                     then
                       let uu____13688 =
                         FStar_List.fold_left
                           (fun s ->
                              fun se1 ->
                                let uu____13697 =
                                  let uu____13699 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.op_Hat uu____13699 "\n" in
                                Prims.op_Hat s uu____13697) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____13688
                     else ());
                    FStar_List.iter
                      (fun se1 ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13709 =
                       let uu____13718 =
                         FStar_Options.use_extracted_interfaces () in
                       if uu____13718
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____13760 se1 =
                            match uu____13760 with
                            | (exports1, hidden1) ->
                                let uu____13788 = for_export env3 hidden1 se1 in
                                (match uu____13788 with
                                 | (se_exported, hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2)) in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1) in
                     match uu____13709 with
                     | (exports1, hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____13942 = acc in
        match uu____13942 with
        | (uu____13977, uu____13978, env1, uu____13980) ->
            let uu____13993 =
              FStar_Util.record_time
                (fun uu____14040 -> process_one_decl acc se) in
            (match uu____13993 with
             | (r, ms_elapsed) ->
                 ((let uu____14106 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ()) in
                   if uu____14106
                   then
                     let uu____14110 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____14112 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14110 uu____14112
                   else ());
                  r)) in
      let uu____14117 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____14117 with
      | (ses1, exports, env1, uu____14165) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env ->
    fun modul ->
      fun exports ->
        let env1 =
          let uu___1831_14203 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1831_14203.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1831_14203.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1831_14203.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1831_14203.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1831_14203.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1831_14203.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1831_14203.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1831_14203.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1831_14203.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1831_14203.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1831_14203.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1831_14203.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1831_14203.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1831_14203.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1831_14203.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1831_14203.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1831_14203.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1831_14203.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1831_14203.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1831_14203.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1831_14203.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1831_14203.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1831_14203.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1831_14203.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1831_14203.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1831_14203.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1831_14203.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1831_14203.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1831_14203.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1831_14203.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1831_14203.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1831_14203.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1831_14203.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1831_14203.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1831_14203.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1831_14203.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1831_14203.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1831_14203.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1831_14203.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1831_14203.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1831_14203.FStar_TypeChecker_Env.strict_args_tab)
          } in
        let check_term lid univs1 t =
          let uu____14223 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____14223 with
          | (univs2, t1) ->
              ((let uu____14231 =
                  let uu____14233 =
                    let uu____14239 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____14239 in
                  FStar_All.pipe_left uu____14233
                    (FStar_Options.Other "Exports") in
                if uu____14231
                then
                  let uu____14243 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____14245 =
                    let uu____14247 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____14247
                      (FStar_String.concat ", ") in
                  let uu____14264 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14243 uu____14245 uu____14264
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____14270 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____14270 (fun a2 -> ()))) in
        let check_term1 lid univs1 t =
          (let uu____14296 =
             let uu____14298 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____14300 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14298 uu____14300 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14296);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____14311) ->
              let uu____14320 =
                let uu____14322 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____14322 in
              if uu____14320
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l, univs1, binders, typ, uu____14336, uu____14337) ->
              let t =
                let uu____14349 =
                  let uu____14356 =
                    let uu____14357 =
                      let uu____14372 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____14372) in
                    FStar_Syntax_Syntax.Tm_arrow uu____14357 in
                  FStar_Syntax_Syntax.mk uu____14356 in
                uu____14349 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l, univs1, t, uu____14388, uu____14389, uu____14390) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) ->
              let uu____14400 =
                let uu____14402 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____14402 in
              if uu____14400 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14410, lbs), uu____14412) ->
              let uu____14423 =
                let uu____14425 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____14425 in
              if uu____14423
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l, univs1, binders, comp, flags) ->
              let uu____14448 =
                let uu____14450 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____14450 in
              if uu____14448
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14471 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14472 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14479 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14480 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14481 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14482 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14489 -> () in
        let uu____14490 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____14490 then () else FStar_List.iter check_sigelt exports
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en ->
    fun m ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption in
      let filter_out_abstract =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) in
      let abstract_inductive_tycons = FStar_Util.mk_ref [] in
      let abstract_inductive_datacons = FStar_Util.mk_ref [] in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l, uu____14596) -> true
             | uu____14598 -> false) quals in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14628 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs', c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14667 ->
                   let uu____14668 =
                     let uu____14675 =
                       let uu____14676 =
                         let uu____14691 = FStar_Syntax_Syntax.mk_Total t in
                         (bs, uu____14691) in
                       FStar_Syntax_Syntax.Tm_arrow uu____14676 in
                     FStar_Syntax_Syntax.mk uu____14675 in
                   uu____14668 FStar_Pervasives_Native.None r) in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, uvs, bs, t, uu____14708, uu____14709) ->
            let s1 =
              let uu___1957_14719 = s in
              let uu____14720 =
                let uu____14721 =
                  let uu____14728 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng in
                  (lid, uvs, uu____14728) in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14721 in
              let uu____14729 =
                let uu____14732 =
                  let uu____14735 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals in
                  FStar_Syntax_Syntax.New :: uu____14735 in
                FStar_Syntax_Syntax.Assumption :: uu____14732 in
              {
                FStar_Syntax_Syntax.sigel = uu____14720;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1957_14719.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14729;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1957_14719.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1957_14719.FStar_Syntax_Syntax.sigattrs)
              } in
            [s1]
        | uu____14738 -> failwith "Impossible!" in
      let val_of_lb s lid uu____14763 lbdef =
        match uu____14763 with
        | (uvs, t) ->
            let attrs =
              let uu____14774 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef in
              if uu____14774
              then
                let uu____14779 =
                  let uu____14780 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_right uu____14780
                    FStar_Syntax_Syntax.fv_to_tm in
                uu____14779 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs in
            let uu___1970_14783 = s in
            let uu____14784 =
              let uu____14787 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals in
              FStar_Syntax_Syntax.Assumption :: uu____14787 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1970_14783.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14784;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1970_14783.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            } in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____14805 -> failwith "Impossible!" in
        let c_opt =
          let uu____14812 = FStar_Syntax_Util.is_unit t in
          if uu____14812
          then
            let uu____14819 = FStar_Syntax_Syntax.mk_Total t in
            FStar_Pervasives_Native.Some uu____14819
          else
            (let uu____14826 =
               let uu____14827 = FStar_Syntax_Subst.compress t in
               uu____14827.FStar_Syntax_Syntax.n in
             match uu____14826 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____14834, c) ->
                 FStar_Pervasives_Native.Some c
             | uu____14858 -> FStar_Pervasives_Native.None) in
        match c_opt with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____14870 = FStar_Syntax_Util.is_lemma_comp c in
            if uu____14870
            then false
            else
              (let uu____14877 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
               if uu____14877
               then true
               else
                 (let uu____14884 = comp_effect_name1 c in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____14884)) in
      let extract_sigelt s =
        (let uu____14896 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme in
         if uu____14896
         then
           let uu____14899 = FStar_Syntax_Print.sigelt_to_string s in
           FStar_Util.print1 "Extracting interface for %s\n" uu____14899
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____14906 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____14926 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____14945 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1 ->
                       fun s1 ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid, uu____14991, uu____14992, uu____14993,
                              uu____14994, uu____14995)
                             ->
                             ((let uu____15005 =
                                 let uu____15008 =
                                   FStar_ST.op_Bang abstract_inductive_tycons in
                                 lid :: uu____15008 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15005);
                              (let uu____15057 =
                                 vals_of_abstract_inductive s1 in
                               FStar_List.append uu____15057 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid, uu____15061, uu____15062, uu____15063,
                              uu____15064, uu____15065)
                             ->
                             ((let uu____15073 =
                                 let uu____15076 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons in
                                 lid :: uu____15076 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15073);
                              sigelts1)
                         | uu____15125 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
             let uu____15134 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____15134
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15144 =
                    let uu___2034_15145 = s in
                    let uu____15146 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2034_15145.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2034_15145.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15146;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2034_15145.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2034_15145.FStar_Syntax_Syntax.sigattrs)
                    } in
                  [uu____15144])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let uu____15157 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____15157
             then []
             else
               (let uu____15164 = lbs in
                match uu____15164 with
                | (flbs, slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef)))) in
                    let is_lemma1 =
                      FStar_List.existsML
                        (fun uu____15226 ->
                           match uu____15226 with
                           | (uu____15234, t, uu____15236) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs in
                    let vals =
                      FStar_List.map2
                        (fun lid ->
                           fun uu____15253 ->
                             match uu____15253 with
                             | (u, t, d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma1
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____15280 ->
                              match uu____15280 with
                              | (uu____15288, t, uu____15290) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid, uu____15302, uu____15303) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15311 = FStar_ST.op_Bang abstract_inductive_tycons in
                 FStar_List.existsML
                   (fun l ->
                      let uu____15340 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l in
                      FStar_Ident.lid_equals lid uu____15340) uu____15311 in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15344 =
                    let uu___2076_15345 = s in
                    let uu____15346 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2076_15345.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2076_15345.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15346;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2076_15345.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2076_15345.FStar_Syntax_Syntax.sigattrs)
                    } in
                  [uu____15344]
                else [])
             else
               (let uu____15353 =
                  let uu___2078_15354 = s in
                  let uu____15355 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2078_15354.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2078_15354.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15355;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2078_15354.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2078_15354.FStar_Syntax_Syntax.sigattrs)
                  } in
                [uu____15353])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15358 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15359 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15360 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15361 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15374 -> [s]) in
      let uu___2090_15375 = m in
      let uu____15376 =
        let uu____15377 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt) in
        FStar_All.pipe_right uu____15377 FStar_List.flatten in
      {
        FStar_Syntax_Syntax.name = (uu___2090_15375.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15376;
        FStar_Syntax_Syntax.exports =
          (uu___2090_15375.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____15428 -> FStar_TypeChecker_Env.snapshot env msg)
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____15475 ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu____15490 = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu____15490
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____15579 = FStar_Options.debug_any () in
       if uu____15579
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let env1 =
         let uu___2115_15595 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2115_15595.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2115_15595.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2115_15595.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2115_15595.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2115_15595.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2115_15595.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2115_15595.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2115_15595.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2115_15595.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2115_15595.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2115_15595.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2115_15595.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2115_15595.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2115_15595.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2115_15595.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2115_15595.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2115_15595.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2115_15595.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2115_15595.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2115_15595.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2115_15595.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2115_15595.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2115_15595.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2115_15595.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2115_15595.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2115_15595.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2115_15595.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2115_15595.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2115_15595.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2115_15595.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2115_15595.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2115_15595.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2115_15595.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2115_15595.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2115_15595.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2115_15595.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2115_15595.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2115_15595.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2115_15595.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2115_15595.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2115_15595.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2115_15595.FStar_TypeChecker_Env.strict_args_tab)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____15597 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____15597 with
       | (ses, exports, env3) ->
           ((let uu___2123_15630 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2123_15630.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2123_15630.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2123_15630.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      fun decls ->
        let uu____15659 = tc_decls env decls in
        match uu____15659 with
        | (ses, exports, env1) ->
            let modul1 =
              let uu___2132_15690 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2132_15690.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2132_15690.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2132_15690.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun m ->
      fun iface_exists ->
        let msg =
          Prims.op_Hat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
        let env01 = push_context env0 msg in
        let uu____15751 = tc_partial_modul env01 m in
        match uu____15751 with
        | (modul, non_private_decls, env) ->
            finish_partial_modul false iface_exists env modul
              non_private_decls
and (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun loading_from_cache ->
    fun iface_exists ->
      fun en ->
        fun m ->
          fun exports ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____15788 = FStar_Errors.get_err_count () in
                 uu____15788 = Prims.int_zero) in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m in
              ((let uu____15799 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low in
                if uu____15799
                then
                  let uu____15803 =
                    let uu____15805 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                    if uu____15805 then "" else " (in lax mode) " in
                  let uu____15813 =
                    let uu____15815 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                    if uu____15815
                    then
                      let uu____15819 =
                        let uu____15821 =
                          FStar_Syntax_Print.modul_to_string m in
                        Prims.op_Hat uu____15821 "\n" in
                      Prims.op_Hat "\nfrom: " uu____15819
                    else "" in
                  let uu____15828 =
                    let uu____15830 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                    if uu____15830
                    then
                      let uu____15834 =
                        let uu____15836 =
                          FStar_Syntax_Print.modul_to_string modul_iface in
                        Prims.op_Hat uu____15836 "\n" in
                      Prims.op_Hat "\nto: " uu____15834
                    else "" in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15803
                    uu____15813 uu____15828
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
                  let en01 =
                    let uu___2158_15850 = en0 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2158_15850.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2158_15850.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2158_15850.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2158_15850.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2158_15850.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2158_15850.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2158_15850.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2158_15850.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2158_15850.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2158_15850.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2158_15850.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2158_15850.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2158_15850.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2158_15850.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2158_15850.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2158_15850.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2158_15850.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2158_15850.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2158_15850.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2158_15850.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2158_15850.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2158_15850.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2158_15850.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2158_15850.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2158_15850.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2158_15850.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2158_15850.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2158_15850.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2158_15850.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2158_15850.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2158_15850.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2158_15850.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2158_15850.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2158_15850.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2158_15850.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2158_15850.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2158_15850.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2158_15850.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2158_15850.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2158_15850.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2158_15850.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2158_15850.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2158_15850.FStar_TypeChecker_Env.strict_args_tab)
                    } in
                  let en02 =
                    let uu___2161_15852 = en01 in
                    let uu____15853 =
                      let uu____15868 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst in
                      (uu____15868, FStar_Pervasives_Native.None) in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2161_15852.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2161_15852.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2161_15852.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2161_15852.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2161_15852.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2161_15852.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2161_15852.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2161_15852.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2161_15852.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2161_15852.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2161_15852.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2161_15852.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2161_15852.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2161_15852.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2161_15852.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2161_15852.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2161_15852.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2161_15852.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2161_15852.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2161_15852.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2161_15852.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2161_15852.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2161_15852.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2161_15852.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2161_15852.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2161_15852.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2161_15852.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2161_15852.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2161_15852.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2161_15852.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2161_15852.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____15853;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2161_15852.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2161_15852.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2161_15852.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2161_15852.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2161_15852.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2161_15852.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2161_15852.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2161_15852.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2161_15852.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2161_15852.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2161_15852.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2161_15852.FStar_TypeChecker_Env.strict_args_tab)
                    } in
                  let uu____15914 =
                    let uu____15916 = FStar_Options.interactive () in
                    Prims.op_Negation uu____15916 in
                  if uu____15914
                  then
                    ((let uu____15920 =
                        FStar_Options.restore_cmd_line_options true in
                      FStar_All.pipe_right uu____15920 (fun a3 -> ()));
                     en02)
                  else en02 in
                let uu____15924 = tc_modul en0 modul_iface true in
                match uu____15924 with
                | (modul_iface1, env) ->
                    ((let uu___2170_15937 = m in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2170_15937.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2170_15937.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2170_15937.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2172_15941 = m in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2172_15941.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2172_15941.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2172_15941.FStar_Syntax_Syntax.is_interface)
                 } in
               let env = FStar_TypeChecker_Env.finish_module en modul in
               (let uu____15944 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____15944 FStar_Util.smap_clear);
               (let uu____15980 =
                  ((let uu____15984 = FStar_Options.lax () in
                    Prims.op_Negation uu____15984) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____15987 =
                       FStar_Options.use_extracted_interfaces () in
                     Prims.op_Negation uu____15987) in
                if uu____15980 then check_exports env modul exports else ());
               (let uu____15993 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str) in
                FStar_All.pipe_right uu____15993 (fun a4 -> ()));
               (modul, env))
let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name in
      let env1 =
        let uu____16008 =
          let uu____16010 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____16010 in
        push_context env uu____16008 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____16031 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____16042 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports in
      match uu____16042 with | (uu____16049, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu____16074 = FStar_Options.debug_any () in
         if uu____16074
         then
           let uu____16077 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16077
         else ());
        (let uu____16089 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
         if uu____16089
         then
           let uu____16092 = FStar_Syntax_Print.modul_to_string m in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16092
         else ());
        (let env1 =
           let uu___2202_16098 = env in
           let uu____16099 =
             let uu____16101 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
             Prims.op_Negation uu____16101 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2202_16098.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2202_16098.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2202_16098.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2202_16098.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2202_16098.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2202_16098.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2202_16098.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2202_16098.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2202_16098.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2202_16098.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2202_16098.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2202_16098.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2202_16098.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2202_16098.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2202_16098.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2202_16098.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2202_16098.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2202_16098.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2202_16098.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2202_16098.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16099;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2202_16098.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2202_16098.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2202_16098.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2202_16098.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2202_16098.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2202_16098.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2202_16098.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2202_16098.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2202_16098.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2202_16098.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2202_16098.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2202_16098.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2202_16098.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2202_16098.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2202_16098.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2202_16098.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2202_16098.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2202_16098.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2202_16098.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2202_16098.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2202_16098.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2202_16098.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2202_16098.FStar_TypeChecker_Env.strict_args_tab)
           } in
         let uu____16103 = tc_modul env1 m b in
         match uu____16103 with
         | (m1, env2) ->
             ((let uu____16115 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
               if uu____16115
               then
                 let uu____16118 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16118
               else ());
              (let uu____16124 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize")) in
               if uu____16124
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1, lbs), ids) ->
                       let n1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses] in
                       let update lb =
                         let uu____16162 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____16162 with
                         | (univnames1, e) ->
                             let uu___2224_16169 = lb in
                             let uu____16170 =
                               let uu____16173 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1 in
                               n1 uu____16173 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16170;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2224_16169.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___2226_16174 = se in
                       let uu____16175 =
                         let uu____16176 =
                           let uu____16183 =
                             let uu____16184 = FStar_List.map update lbs in
                             (b1, uu____16184) in
                           (uu____16183, ids) in
                         FStar_Syntax_Syntax.Sig_let uu____16176 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16175;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2226_16174.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2226_16174.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2226_16174.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2226_16174.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16192 -> se in
                 let normalized_module =
                   let uu___2230_16194 = m1 in
                   let uu____16195 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2230_16194.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16195;
                     FStar_Syntax_Syntax.exports =
                       (uu___2230_16194.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2230_16194.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____16196 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____16196
               else ());
              (m1, env2)))