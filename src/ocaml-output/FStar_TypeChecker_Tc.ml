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
        else Prims.int_zero  in
      let uu____64 = FStar_Options.reuse_hint_for ()  in
      match uu____64 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____72 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____72 l  in
          let uu___16_73 = env  in
          let uu____74 =
            let uu____89 =
              let uu____97 = let uu____103 = get_n lid  in (lid, uu____103)
                 in
              FStar_Pervasives_Native.Some uu____97  in
            (tbl, uu____89)  in
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
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____126 = FStar_TypeChecker_Env.current_module env  in
                let uu____127 =
                  let uu____129 = FStar_Ident.next_id ()  in
                  FStar_All.pipe_right uu____129 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____126 uu____127
            | l::uu____134 -> l  in
          let uu___25_137 = env  in
          let uu____138 =
            let uu____153 =
              let uu____161 = let uu____167 = get_n lid  in (lid, uu____167)
                 in
              FStar_Pervasives_Native.Some uu____161  in
            (tbl, uu____153)  in
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
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____193 =
         let uu____195 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____195  in
       Prims.op_Negation uu____193)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____212 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____212 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____242 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____242
         then
           let uu____246 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____246
         else ());
        (let uu____251 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____251 with
         | (t',uu____259,uu____260) ->
             ((let uu____262 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____262
               then
                 let uu____266 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____266
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
        let uu____287 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____287
  
let check_nogen :
  'Auu____297 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____297 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____320 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1
           in
        ([], uu____320)
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____356 =
          let uu____357 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____363 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____357 uu____363  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____407)::(wp,uu____409)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____438 -> fail1 ())
        | uu____439 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____451 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____451 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____483 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____483 t  in
          let open_univs_binders n_binders bs =
            let uu____499 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____499 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____509 =
            let uu____516 =
              open_univs_binders Prims.int_zero
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____518 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____516 uu____518  in
          (match uu____509 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____523 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____523 with
                | (effect_params,env1,uu____532) ->
                    let uu____533 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____533 with
                     | (signature,uu____539) ->
                         let ed1 =
                           let uu___98_541 = ed  in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___98_541.FStar_Syntax_Syntax.is_layered);
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
                             FStar_Syntax_Syntax.stronger =
                               (uu___98_541.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.match_wps =
                               (uu___98_541.FStar_Syntax_Syntax.match_wps);
                             FStar_Syntax_Syntax.trivial =
                               (uu___98_541.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___98_541.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___98_541.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___98_541.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.stronger_repr =
                               (uu___98_541.FStar_Syntax_Syntax.stronger_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___98_541.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___98_541.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____569 ->
                               let op uu____601 =
                                 match uu____601 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____621 =
                                       let uu____622 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____625 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____622
                                         uu____625
                                        in
                                     (us, uu____621)
                                  in
                               let uu___110_628 = ed1  in
                               let uu____629 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____630 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____631 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____632 =
                                 FStar_Syntax_Util.map_match_wps op
                                   ed1.FStar_Syntax_Syntax.match_wps
                                  in
                               let uu____637 =
                                 FStar_Util.map_opt
                                   ed1.FStar_Syntax_Syntax.trivial op
                                  in
                               let uu____640 =
                                 let uu____641 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____641  in
                               let uu____652 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____653 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____654 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___113_662 = a  in
                                      let uu____663 =
                                        let uu____664 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____664
                                         in
                                      let uu____675 =
                                        let uu____676 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____676
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___113_662.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___113_662.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___113_662.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___113_662.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____663;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____675
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.is_layered =
                                   (uu___110_628.FStar_Syntax_Syntax.is_layered);
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
                                 FStar_Syntax_Syntax.stronger = uu____631;
                                 FStar_Syntax_Syntax.match_wps = uu____632;
                                 FStar_Syntax_Syntax.trivial = uu____637;
                                 FStar_Syntax_Syntax.repr = uu____640;
                                 FStar_Syntax_Syntax.return_repr = uu____652;
                                 FStar_Syntax_Syntax.bind_repr = uu____653;
                                 FStar_Syntax_Syntax.stronger_repr =
                                   (uu___110_628.FStar_Syntax_Syntax.stronger_repr);
                                 FStar_Syntax_Syntax.actions = uu____654;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___110_628.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____721 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____727 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____721 uu____727  in
                           let uu____734 =
                             let uu____735 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____735.FStar_Syntax_Syntax.n  in
                           match uu____734 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____774)::(wp,uu____776)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____805 -> fail1 signature1)
                           | uu____806 -> fail1 signature1  in
                         let uu____807 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____807 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____831 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____838 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____838 with
                                     | (signature1,uu____850) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____851 ->
                                    let uu____854 =
                                      let uu____859 =
                                        let uu____860 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____860)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____859
                                       in
                                    (match uu____854 with
                                     | (uu____873,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____876 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____876
                                 in
                              ((let uu____878 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____878
                                then
                                  let uu____883 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____885 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____888 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____890 =
                                    let uu____892 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____892
                                     in
                                  let uu____893 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____883 uu____885 uu____888 uu____890
                                    uu____893
                                else ());
                               (let check_and_gen' env3 uu____928 k =
                                  match uu____928 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____964::uu____965 ->
                                           let uu____968 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____968 with
                                            | (us1,t1) ->
                                                let uu____991 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____991 with
                                                 | (us2,t2) ->
                                                     let uu____1006 =
                                                       let uu____1007 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____1007 t2 k
                                                        in
                                                     let uu____1008 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____1008))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____1027 =
                                      let uu____1036 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1043 =
                                        let uu____1052 =
                                          let uu____1059 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1059
                                           in
                                        [uu____1052]  in
                                      uu____1036 :: uu____1043  in
                                    let uu____1078 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____1027
                                      uu____1078
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____1082 = fresh_effect_signature ()
                                     in
                                  match uu____1082 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____1098 =
                                          let uu____1107 =
                                            let uu____1114 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1114
                                             in
                                          [uu____1107]  in
                                        let uu____1127 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1098
                                          uu____1127
                                         in
                                      let expected_k =
                                        let uu____1133 =
                                          let uu____1142 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____1149 =
                                            let uu____1158 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1165 =
                                              let uu____1174 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____1181 =
                                                let uu____1190 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1197 =
                                                  let uu____1206 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____1206]  in
                                                uu____1190 :: uu____1197  in
                                              uu____1174 :: uu____1181  in
                                            uu____1158 :: uu____1165  in
                                          uu____1142 :: uu____1149  in
                                        let uu____1249 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1133
                                          uu____1249
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let uu____1252 =
                                  FStar_Syntax_Util.get_match_with_close_wps
                                    ed2.FStar_Syntax_Syntax.match_wps
                                   in
                                match uu____1252 with
                                | (if_then_else1,ite_wp,close_wp) ->
                                    let if_then_else2 =
                                      let p =
                                        let uu____1272 =
                                          let uu____1275 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1275
                                           in
                                        let uu____1276 =
                                          let uu____1277 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____1277
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____1272
                                          uu____1276
                                         in
                                      let expected_k =
                                        let uu____1289 =
                                          let uu____1298 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1305 =
                                            let uu____1314 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____1321 =
                                              let uu____1330 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____1337 =
                                                let uu____1346 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____1346]  in
                                              uu____1330 :: uu____1337  in
                                            uu____1314 :: uu____1321  in
                                          uu____1298 :: uu____1305  in
                                        let uu____1383 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____1289
                                          uu____1383
                                         in
                                      check_and_gen' env2 if_then_else1
                                        expected_k
                                       in
                                    let ite_wp1 =
                                      let expected_k =
                                        let uu____1398 =
                                          let uu____1407 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1414 =
                                            let uu____1423 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1423]  in
                                          uu____1407 :: uu____1414  in
                                        let uu____1448 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____1398
                                          uu____1448
                                         in
                                      check_and_gen' env2 ite_wp expected_k
                                       in
                                    let close_wp1 =
                                      let b =
                                        let uu____1461 =
                                          let uu____1464 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1464
                                           in
                                        let uu____1465 =
                                          let uu____1466 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____1466
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____1461
                                          uu____1465
                                         in
                                      let b_wp_a =
                                        let uu____1478 =
                                          let uu____1487 =
                                            let uu____1494 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1494
                                             in
                                          [uu____1487]  in
                                        let uu____1507 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____1478
                                          uu____1507
                                         in
                                      let expected_k =
                                        let uu____1513 =
                                          let uu____1522 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1529 =
                                            let uu____1538 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____1545 =
                                              let uu____1554 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____1554]  in
                                            uu____1538 :: uu____1545  in
                                          uu____1522 :: uu____1529  in
                                        let uu____1585 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____1513
                                          uu____1585
                                         in
                                      check_and_gen' env2 close_wp expected_k
                                       in
                                    let stronger =
                                      let uu____1589 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____1589 with
                                      | (t,uu____1595) ->
                                          let expected_k =
                                            let uu____1599 =
                                              let uu____1608 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____1615 =
                                                let uu____1624 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1631 =
                                                  let uu____1640 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1640]  in
                                                uu____1624 :: uu____1631  in
                                              uu____1608 :: uu____1615  in
                                            let uu____1671 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____1599 uu____1671
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let trivial_wp =
                                      match ed2.FStar_Syntax_Syntax.trivial
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some trivial
                                          ->
                                          let uu____1680 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____1680 with
                                           | (t,uu____1688) ->
                                               let expected_k =
                                                 let uu____1692 =
                                                   let uu____1701 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a
                                                      in
                                                   let uu____1708 =
                                                     let uu____1717 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         wp_a
                                                        in
                                                     [uu____1717]  in
                                                   uu____1701 :: uu____1708
                                                    in
                                                 let uu____1742 =
                                                   FStar_Syntax_Syntax.mk_GTotal
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____1692 uu____1742
                                                  in
                                               let uu____1745 =
                                                 check_and_gen' env2 trivial
                                                   expected_k
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____1745)
                                       in
                                    let uu____1746 =
                                      let uu____1759 =
                                        let uu____1760 =
                                          FStar_Syntax_Subst.compress
                                            ed2.FStar_Syntax_Syntax.repr
                                           in
                                        uu____1760.FStar_Syntax_Syntax.n  in
                                      match uu____1759 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          ((ed2.FStar_Syntax_Syntax.repr),
                                            (ed2.FStar_Syntax_Syntax.bind_repr),
                                            (ed2.FStar_Syntax_Syntax.return_repr),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____1779 ->
                                          let repr =
                                            let uu____1781 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____1781 with
                                            | (t,uu____1787) ->
                                                let expected_k =
                                                  let uu____1791 =
                                                    let uu____1800 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____1807 =
                                                      let uu____1816 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____1816]  in
                                                    uu____1800 :: uu____1807
                                                     in
                                                  let uu____1841 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____1791 uu____1841
                                                   in
                                                tc_check_trivial_guard env2
                                                  ed2.FStar_Syntax_Syntax.repr
                                                  expected_k
                                             in
                                          let mk_repr' t wp =
                                            let repr1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2 repr
                                               in
                                            let uu____1858 =
                                              let uu____1865 =
                                                let uu____1866 =
                                                  let uu____1883 =
                                                    let uu____1894 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____1903 =
                                                      let uu____1914 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____1914]  in
                                                    uu____1894 :: uu____1903
                                                     in
                                                  (repr1, uu____1883)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____1866
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____1865
                                               in
                                            uu____1858
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____1972 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____1972 wp  in
                                          let destruct_repr t =
                                            let uu____1987 =
                                              let uu____1988 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____1988.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1987 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____1999,(t1,uu____2001)::
                                                 (wp,uu____2003)::[])
                                                -> (t1, wp)
                                            | uu____2062 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____2074 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____2074
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____2075 =
                                              fresh_effect_signature ()  in
                                            match uu____2075 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____2091 =
                                                    let uu____2100 =
                                                      let uu____2107 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____2107
                                                       in
                                                    [uu____2100]  in
                                                  let uu____2120 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____2091 uu____2120
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
                                                  let uu____2128 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____2128
                                                   in
                                                let wp_g_x =
                                                  let uu____2133 =
                                                    let uu____2138 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____2139 =
                                                      let uu____2140 =
                                                        let uu____2149 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____2149
                                                         in
                                                      [uu____2140]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____2138 uu____2139
                                                     in
                                                  uu____2133
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____2180 =
                                                      let uu____2185 =
                                                        let uu____2186 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2186
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____2195 =
                                                        let uu____2196 =
                                                          let uu____2199 =
                                                            let uu____2202 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____2203 =
                                                              let uu____2206
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____2207
                                                                =
                                                                let uu____2210
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____2211
                                                                  =
                                                                  let uu____2214
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____2214]
                                                                   in
                                                                uu____2210 ::
                                                                  uu____2211
                                                                 in
                                                              uu____2206 ::
                                                                uu____2207
                                                               in
                                                            uu____2202 ::
                                                              uu____2203
                                                             in
                                                          r :: uu____2199  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____2196
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____2185 uu____2195
                                                       in
                                                    uu____2180
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____2232 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____2232
                                                  then
                                                    let uu____2243 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____2250 =
                                                      let uu____2259 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____2259]  in
                                                    uu____2243 :: uu____2250
                                                  else []  in
                                                let expected_k =
                                                  let uu____2295 =
                                                    let uu____2304 =
                                                      let uu____2313 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____2320 =
                                                        let uu____2329 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____2329]  in
                                                      uu____2313 ::
                                                        uu____2320
                                                       in
                                                    let uu____2354 =
                                                      let uu____2363 =
                                                        let uu____2372 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____2379 =
                                                          let uu____2388 =
                                                            let uu____2395 =
                                                              let uu____2396
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____2396
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2395
                                                             in
                                                          let uu____2397 =
                                                            let uu____2406 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____2413 =
                                                              let uu____2422
                                                                =
                                                                let uu____2429
                                                                  =
                                                                  let uu____2430
                                                                    =
                                                                    let uu____2439
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____2439]
                                                                     in
                                                                  let uu____2458
                                                                    =
                                                                    let uu____2461
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____2461
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____2430
                                                                    uu____2458
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____2429
                                                                 in
                                                              [uu____2422]
                                                               in
                                                            uu____2406 ::
                                                              uu____2413
                                                             in
                                                          uu____2388 ::
                                                            uu____2397
                                                           in
                                                        uu____2372 ::
                                                          uu____2379
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____2363
                                                       in
                                                    FStar_List.append
                                                      uu____2304 uu____2354
                                                     in
                                                  let uu____2506 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____2295 uu____2506
                                                   in
                                                let uu____2509 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____2509 with
                                                 | (expected_k1,uu____2517,uu____2518)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___249_2525 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___249_2525.FStar_TypeChecker_Env.strict_args_tab)
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
                                              let uu____2538 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____2538
                                               in
                                            let res =
                                              let wp =
                                                let uu____2546 =
                                                  let uu____2551 =
                                                    let uu____2552 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2552
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____2561 =
                                                    let uu____2562 =
                                                      let uu____2565 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____2566 =
                                                        let uu____2569 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____2569]  in
                                                      uu____2565 ::
                                                        uu____2566
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2562
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2551 uu____2561
                                                   in
                                                uu____2546
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____2581 =
                                                let uu____2590 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____2597 =
                                                  let uu____2606 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____2606]  in
                                                uu____2590 :: uu____2597  in
                                              let uu____2631 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2581 uu____2631
                                               in
                                            let uu____2634 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____2634 with
                                            | (expected_k1,uu____2642,uu____2643)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____2649 =
                                                  check_and_gen' env3
                                                    ed2.FStar_Syntax_Syntax.return_repr
                                                    expected_k1
                                                   in
                                                (match uu____2649 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____2672 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____2687 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____2701 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____2701 with
                                                   | (usubst,uvs) ->
                                                       let uu____2724 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____2725 =
                                                         let uu___278_2726 =
                                                           act  in
                                                         let uu____2727 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____2728 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____2729 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___278_2726.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___278_2726.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____2727;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____2728;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____2729
                                                         }  in
                                                       (uu____2724,
                                                         uu____2725))
                                                 in
                                              match uu____2687 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____2733 =
                                                      let uu____2734 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____2734.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2733 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____2760 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____2760
                                                        then
                                                          let uu____2763 =
                                                            let uu____2766 =
                                                              let uu____2767
                                                                =
                                                                let uu____2768
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____2768
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____2767
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____2766
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____2763
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____2791 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____2792 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____2792 with
                                                   | (act_typ1,uu____2800,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___295_2803 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___295_2803.FStar_TypeChecker_Env.strict_args_tab)
                                                         }  in
                                                       ((let uu____2806 =
                                                           FStar_TypeChecker_Env.debug
                                                             env3
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____2806
                                                         then
                                                           let uu____2810 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____2812 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____2814 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____2810
                                                             uu____2812
                                                             uu____2814
                                                         else ());
                                                        (let uu____2819 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____2819
                                                         with
                                                         | (act_defn,uu____2827,g_a)
                                                             ->
                                                             let act_defn1 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                 env3
                                                                 act_defn
                                                                in
                                                             let act_typ2 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                 FStar_TypeChecker_Env.Eager_unfolding;
                                                                 FStar_TypeChecker_Env.Beta]
                                                                 env3
                                                                 act_typ1
                                                                in
                                                             let uu____2831 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____2867
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____2867
                                                                    with
                                                                    | 
                                                                    (bs1,uu____2879)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____2886
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2886
                                                                     in
                                                                    let uu____2889
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____2889
                                                                    with
                                                                    | 
                                                                    (k1,uu____2903,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____2907
                                                                   ->
                                                                   let uu____2908
                                                                    =
                                                                    let uu____2914
                                                                    =
                                                                    let uu____2916
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____2918
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____2916
                                                                    uu____2918
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____2914)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____2908
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____2831
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____2936
                                                                    =
                                                                    let uu____2937
                                                                    =
                                                                    let uu____2938
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____2938
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____2937
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____2936);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2941
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____2941.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____2940
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____2966
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____2966
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____2973
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____2973
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____2993
                                                                    =
                                                                    let uu____2994
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____2994]
                                                                     in
                                                                    let uu____2995
                                                                    =
                                                                    let uu____3006
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____3006]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2993;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2995;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____3031
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3031))
                                                                    | 
                                                                    uu____3034
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____3036
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____3058
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____3058))
                                                                     in
                                                                    match uu____3036
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env3
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___345_3077
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___345_3077.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___345_3077.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___345_3077.FStar_Syntax_Syntax.action_params);
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
                                          (repr, bind_repr, return_repr,
                                            actions)
                                       in
                                    (match uu____1746 with
                                     | (repr,bind_repr,return_repr,actions)
                                         ->
                                         let t0 =
                                           let uu____3101 =
                                             FStar_Syntax_Syntax.mk_Total
                                               ed2.FStar_Syntax_Syntax.signature
                                              in
                                           FStar_Syntax_Util.arrow
                                             ed2.FStar_Syntax_Syntax.binders
                                             uu____3101
                                            in
                                         let uu____3104 =
                                           let uu____3109 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env0 t0
                                              in
                                           match uu____3109 with
                                           | (gen_univs,t) ->
                                               (match annotated_univ_names
                                                with
                                                | [] -> (gen_univs, t)
                                                | uu____3128 ->
                                                    let uu____3131 =
                                                      ((FStar_List.length
                                                          gen_univs)
                                                         =
                                                         (FStar_List.length
                                                            annotated_univ_names))
                                                        &&
                                                        (FStar_List.forall2
                                                           (fun u1  ->
                                                              fun u2  ->
                                                                let uu____3138
                                                                  =
                                                                  FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2
                                                                   in
                                                                uu____3138 =
                                                                  Prims.int_zero)
                                                           gen_univs
                                                           annotated_univ_names)
                                                       in
                                                    if uu____3131
                                                    then (gen_univs, t)
                                                    else
                                                      (let uu____3149 =
                                                         let uu____3155 =
                                                           let uu____3157 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  annotated_univ_names)
                                                              in
                                                           let uu____3159 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  gen_univs)
                                                              in
                                                           FStar_Util.format2
                                                             "Expected an effect definition with %s universes; but found %s"
                                                             uu____3157
                                                             uu____3159
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                           uu____3155)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____3149
                                                         (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                            in
                                         (match uu____3104 with
                                          | (univs1,t) ->
                                              let signature1 =
                                                let uu____3170 =
                                                  let uu____3183 =
                                                    let uu____3184 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____3184.FStar_Syntax_Syntax.n
                                                     in
                                                  (effect_params, uu____3183)
                                                   in
                                                match uu____3170 with
                                                | ([],uu____3195) -> t
                                                | (uu____3210,FStar_Syntax_Syntax.Tm_arrow
                                                   (uu____3211,c)) ->
                                                    FStar_Syntax_Util.comp_result
                                                      c
                                                | uu____3249 ->
                                                    failwith
                                                      "Impossible : t is an arrow"
                                                 in
                                              let close1 n1 ts =
                                                let ts1 =
                                                  let uu____3277 =
                                                    FStar_Syntax_Subst.close_tscheme
                                                      effect_params ts
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars_tscheme
                                                    univs1 uu____3277
                                                   in
                                                let m =
                                                  FStar_List.length
                                                    (FStar_Pervasives_Native.fst
                                                       ts1)
                                                   in
                                                (let uu____3284 =
                                                   ((n1 >= Prims.int_zero) &&
                                                      (let uu____3288 =
                                                         FStar_Syntax_Util.is_unknown
                                                           (FStar_Pervasives_Native.snd
                                                              ts1)
                                                          in
                                                       Prims.op_Negation
                                                         uu____3288))
                                                     && (m <> n1)
                                                    in
                                                 if uu____3284
                                                 then
                                                   let error =
                                                     if m < n1
                                                     then
                                                       "not universe-polymorphic enough"
                                                     else
                                                       "too universe-polymorphic"
                                                      in
                                                   let err_msg =
                                                     let uu____3306 =
                                                       FStar_Util.string_of_int
                                                         m
                                                        in
                                                     let uu____3308 =
                                                       FStar_Util.string_of_int
                                                         n1
                                                        in
                                                     let uu____3310 =
                                                       FStar_Syntax_Print.tscheme_to_string
                                                         ts1
                                                        in
                                                     FStar_Util.format4
                                                       "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                       error uu____3306
                                                       uu____3308 uu____3310
                                                      in
                                                   FStar_Errors.raise_error
                                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                       err_msg)
                                                     (FStar_Pervasives_Native.snd
                                                        ts1).FStar_Syntax_Syntax.pos
                                                 else ());
                                                ts1  in
                                              let close_action act =
                                                let uu____3326 =
                                                  close1 (~- Prims.int_one)
                                                    ((act.FStar_Syntax_Syntax.action_univs),
                                                      (act.FStar_Syntax_Syntax.action_defn))
                                                   in
                                                match uu____3326 with
                                                | (univs2,defn) ->
                                                    let uu____3342 =
                                                      close1
                                                        (~- Prims.int_one)
                                                        ((act.FStar_Syntax_Syntax.action_univs),
                                                          (act.FStar_Syntax_Syntax.action_typ))
                                                       in
                                                    (match uu____3342 with
                                                     | (univs',typ) ->
                                                         let uu___395_3359 =
                                                           act  in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___395_3359.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___395_3359.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = univs2;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___395_3359.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = defn;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = typ
                                                         })
                                                 in
                                              let match_wps =
                                                let uu____3366 =
                                                  let uu____3367 =
                                                    close1 Prims.int_zero
                                                      if_then_else2
                                                     in
                                                  let uu____3369 =
                                                    close1 Prims.int_zero
                                                      ite_wp1
                                                     in
                                                  let uu____3371 =
                                                    close1 Prims.int_one
                                                      close_wp1
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.if_then_else
                                                      = uu____3367;
                                                    FStar_Syntax_Syntax.ite_wp
                                                      = uu____3369;
                                                    FStar_Syntax_Syntax.close_wp
                                                      = uu____3371
                                                  }  in
                                                FStar_Util.Inl uu____3366  in
                                              let ed3 =
                                                let uu___399_3374 = ed2  in
                                                let uu____3375 =
                                                  close1 Prims.int_zero
                                                    return_wp
                                                   in
                                                let uu____3377 =
                                                  close1 Prims.int_one
                                                    bind_wp
                                                   in
                                                let uu____3379 =
                                                  close1 Prims.int_zero
                                                    stronger
                                                   in
                                                let uu____3381 =
                                                  FStar_Util.map_opt
                                                    trivial_wp
                                                    (close1 Prims.int_zero)
                                                   in
                                                let uu____3385 =
                                                  let uu____3386 =
                                                    close1 Prims.int_zero
                                                      ([], repr)
                                                     in
                                                  FStar_Pervasives_Native.snd
                                                    uu____3386
                                                   in
                                                let uu____3404 =
                                                  close1 Prims.int_zero
                                                    return_repr
                                                   in
                                                let uu____3406 =
                                                  close1 Prims.int_one
                                                    bind_repr
                                                   in
                                                let uu____3408 =
                                                  FStar_List.map close_action
                                                    actions
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.is_layered
                                                    =
                                                    (uu___399_3374.FStar_Syntax_Syntax.is_layered);
                                                  FStar_Syntax_Syntax.cattributes
                                                    =
                                                    (uu___399_3374.FStar_Syntax_Syntax.cattributes);
                                                  FStar_Syntax_Syntax.mname =
                                                    (uu___399_3374.FStar_Syntax_Syntax.mname);
                                                  FStar_Syntax_Syntax.univs =
                                                    univs1;
                                                  FStar_Syntax_Syntax.binders
                                                    = effect_params;
                                                  FStar_Syntax_Syntax.signature
                                                    = signature1;
                                                  FStar_Syntax_Syntax.ret_wp
                                                    = uu____3375;
                                                  FStar_Syntax_Syntax.bind_wp
                                                    = uu____3377;
                                                  FStar_Syntax_Syntax.stronger
                                                    = uu____3379;
                                                  FStar_Syntax_Syntax.match_wps
                                                    = match_wps;
                                                  FStar_Syntax_Syntax.trivial
                                                    = uu____3381;
                                                  FStar_Syntax_Syntax.repr =
                                                    uu____3385;
                                                  FStar_Syntax_Syntax.return_repr
                                                    = uu____3404;
                                                  FStar_Syntax_Syntax.bind_repr
                                                    = uu____3406;
                                                  FStar_Syntax_Syntax.stronger_repr
                                                    =
                                                    (uu___399_3374.FStar_Syntax_Syntax.stronger_repr);
                                                  FStar_Syntax_Syntax.actions
                                                    = uu____3408;
                                                  FStar_Syntax_Syntax.eff_attrs
                                                    =
                                                    (uu___399_3374.FStar_Syntax_Syntax.eff_attrs)
                                                }  in
                                              ((let uu____3412 =
                                                  (FStar_TypeChecker_Env.debug
                                                     env2 FStar_Options.Low)
                                                    ||
                                                    (FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env2)
                                                       (FStar_Options.Other
                                                          "ED"))
                                                   in
                                                if uu____3412
                                                then
                                                  let uu____3417 =
                                                    FStar_Syntax_Print.eff_decl_to_string
                                                      false ed3
                                                     in
                                                  FStar_Util.print_string
                                                    uu____3417
                                                else ());
                                               ed3)))))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____3443 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____3443 with
      | (effect_binders_un,signature_un) ->
          let uu____3460 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3460 with
           | (effect_binders,env1,uu____3479) ->
               let uu____3480 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3480 with
                | (signature,uu____3496) ->
                    let raise_error1 uu____3512 =
                      match uu____3512 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3548  ->
                           match uu____3548 with
                           | (bv,qual) ->
                               let uu____3567 =
                                 let uu___424_3568 = bv  in
                                 let uu____3569 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___424_3568.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___424_3568.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3569
                                 }  in
                               (uu____3567, qual)) effect_binders
                       in
                    let uu____3574 =
                      let uu____3581 =
                        let uu____3582 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3582.FStar_Syntax_Syntax.n  in
                      match uu____3581 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3592)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3624 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3574 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3650 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3650
                           then
                             let uu____3653 =
                               let uu____3656 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3656  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3653
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3704 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3704 with
                           | (t2,comp,uu____3717) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3726 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____3726 with
                          | (repr,_comp) ->
                              ((let uu____3750 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3750
                                then
                                  let uu____3754 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3754
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
                                let uu____3761 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____3764 =
                                    let uu____3765 =
                                      let uu____3766 =
                                        let uu____3783 =
                                          let uu____3794 =
                                            let uu____3803 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____3806 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____3803, uu____3806)  in
                                          [uu____3794]  in
                                        (wp_type, uu____3783)  in
                                      FStar_Syntax_Syntax.Tm_app uu____3766
                                       in
                                    mk1 uu____3765  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____3764
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____3854 =
                                      let uu____3861 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____3861)  in
                                    let uu____3867 =
                                      let uu____3876 =
                                        let uu____3883 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____3883
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____3876]  in
                                    uu____3854 :: uu____3867  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____3920 =
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
                                  let uu____3986 = item  in
                                  match uu____3986 with
                                  | (u_item,item1) ->
                                      let uu____4001 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____4001 with
                                       | (item2,item_comp) ->
                                           ((let uu____4017 =
                                               let uu____4019 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____4019
                                                in
                                             if uu____4017
                                             then
                                               let uu____4022 =
                                                 let uu____4028 =
                                                   let uu____4030 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____4032 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____4030 uu____4032
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____4028)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____4022
                                             else ());
                                            (let uu____4038 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____4038 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____4056 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____4058 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____4060 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____4060 with
                                | (dmff_env1,uu____4086,bind_wp,bind_elab) ->
                                    let uu____4089 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____4089 with
                                     | (dmff_env2,uu____4115,return_wp,return_elab)
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
                                           let uu____4124 =
                                             let uu____4125 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4125.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4124 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4183 =
                                                 let uu____4202 =
                                                   let uu____4207 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____4207
                                                    in
                                                 match uu____4202 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____4289 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____4183 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____4343 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4343 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4366 =
                                                          let uu____4367 =
                                                            let uu____4384 =
                                                              let uu____4395
                                                                =
                                                                let uu____4404
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____4409
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4404,
                                                                  uu____4409)
                                                                 in
                                                              [uu____4395]
                                                               in
                                                            (wp_type,
                                                              uu____4384)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4367
                                                           in
                                                        mk1 uu____4366  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____4445 =
                                                      let uu____4454 =
                                                        let uu____4455 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4455
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4454
                                                       in
                                                    (match uu____4445 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____4478
                                                           =
                                                           let error_msg =
                                                             let uu____4481 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____4483 =
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
                                                               uu____4481
                                                               uu____4483
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
                                                               ((let uu____4493
                                                                   =
                                                                   let uu____4495
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____4495
                                                                    in
                                                                 if
                                                                   uu____4493
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4500
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
                                                                   uu____4500
                                                                   (fun a1 
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
                                                             let uu____4529 =
                                                               let uu____4534
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____4535
                                                                 =
                                                                 let uu____4536
                                                                   =
                                                                   let uu____4545
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____4545,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____4536]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4534
                                                                 uu____4535
                                                                in
                                                             uu____4529
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____4580 =
                                                             let uu____4581 =
                                                               let uu____4590
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4590]
                                                                in
                                                             b11 ::
                                                               uu____4581
                                                              in
                                                           let uu____4615 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____4580
                                                             uu____4615
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4618 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4626 =
                                             let uu____4627 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4627.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4626 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4685 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4685
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4706 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4714 =
                                             let uu____4715 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4715.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4714 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____4749 =
                                                 let uu____4750 =
                                                   let uu____4759 =
                                                     let uu____4766 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4766
                                                      in
                                                   [uu____4759]  in
                                                 FStar_List.append uu____4750
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____4749 body what
                                           | uu____4785 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu____4815 =
                                                let uu____4816 =
                                                  let uu____4817 =
                                                    let uu____4834 =
                                                      let uu____4845 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4845
                                                       in
                                                    (t, uu____4834)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4817
                                                   in
                                                mk1 uu____4816  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4815)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4903 = f a2  in
                                               [uu____4903]
                                           | x::xs ->
                                               let uu____4914 =
                                                 apply_last1 f xs  in
                                               x :: uu____4914
                                            in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange
                                              in
                                           let uu____4948 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____4948 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____4978 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____4978
                                                 then
                                                   let uu____4981 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____4981
                                                 else ());
                                                (let uu____4986 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____4986))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____4995 =
                                                 let uu____5000 = mk_lid name
                                                    in
                                                 let uu____5001 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____5000 uu____5001
                                                  in
                                               (match uu____4995 with
                                                | (sigelt,fv) ->
                                                    ((let uu____5005 =
                                                        let uu____5008 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____5008
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____5005);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____5062 =
                                             let uu____5065 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____5068 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____5065 :: uu____5068  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____5062);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____5120 =
                                              let uu____5123 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____5124 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____5123 :: uu____5124  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____5120);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____5176 =
                                               let uu____5179 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____5182 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____5179 :: uu____5182  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____5176);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____5234 =
                                                let uu____5237 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____5238 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____5237 :: uu____5238  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____5234);
                                             (let uu____5287 =
                                                FStar_List.fold_left
                                                  (fun uu____5327  ->
                                                     fun action  ->
                                                       match uu____5327 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____5348 =
                                                             let uu____5355 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____5355
                                                               params_un
                                                              in
                                                           (match uu____5348
                                                            with
                                                            | (action_params,env',uu____5364)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____5390
                                                                     ->
                                                                    match uu____5390
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____5409
                                                                    =
                                                                    let uu___617_5410
                                                                    = bv  in
                                                                    let uu____5411
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___617_5410.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___617_5410.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____5411
                                                                    }  in
                                                                    (uu____5409,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____5417
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____5417
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
                                                                    uu____5456
                                                                    ->
                                                                    let uu____5457
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5457
                                                                     in
                                                                    ((
                                                                    let uu____5461
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____5461
                                                                    then
                                                                    let uu____5466
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____5469
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____5472
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5474
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5466
                                                                    uu____5469
                                                                    uu____5472
                                                                    uu____5474
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5483
                                                                    =
                                                                    let uu____5486
                                                                    =
                                                                    let uu___639_5487
                                                                    = action
                                                                     in
                                                                    let uu____5488
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____5489
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___639_5487.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___639_5487.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___639_5487.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5488;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5489
                                                                    }  in
                                                                    uu____5486
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____5483))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____5287 with
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
                                                      let uu____5533 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____5540 =
                                                        let uu____5549 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____5549]  in
                                                      uu____5533 ::
                                                        uu____5540
                                                       in
                                                    let uu____5574 =
                                                      let uu____5577 =
                                                        let uu____5578 =
                                                          let uu____5579 =
                                                            let uu____5596 =
                                                              let uu____5607
                                                                =
                                                                let uu____5616
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____5619
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____5616,
                                                                  uu____5619)
                                                                 in
                                                              [uu____5607]
                                                               in
                                                            (repr,
                                                              uu____5596)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5579
                                                           in
                                                        mk1 uu____5578  in
                                                      let uu____5655 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____5577
                                                        uu____5655
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____5574
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____5656 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____5660 =
                                                    let uu____5669 =
                                                      let uu____5670 =
                                                        let uu____5673 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____5673
                                                         in
                                                      uu____5670.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5669 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____5687)
                                                        ->
                                                        let uu____5724 =
                                                          let uu____5745 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____5745
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____5813 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____5724
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____5878 =
                                                               let uu____5879
                                                                 =
                                                                 let uu____5882
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5882
                                                                  in
                                                               uu____5879.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____5878
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____5915
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____5915
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____5930
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5961
                                                                     ->
                                                                    match uu____5961
                                                                    with
                                                                    | 
                                                                    (bv,uu____5970)
                                                                    ->
                                                                    let uu____5975
                                                                    =
                                                                    let uu____5977
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5977
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5975
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____5930
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
                                                                    let uu____6069
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____6069
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____6079
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6090
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____6090
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____6100
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____6103
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____6100,
                                                                    uu____6103)))
                                                              | uu____6118 ->
                                                                  let uu____6119
                                                                    =
                                                                    let uu____6125
                                                                    =
                                                                    let uu____6127
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____6127
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____6125)
                                                                     in
                                                                  raise_error1
                                                                    uu____6119))
                                                    | uu____6139 ->
                                                        let uu____6140 =
                                                          let uu____6146 =
                                                            let uu____6148 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____6148
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____6146)
                                                           in
                                                        raise_error1
                                                          uu____6140
                                                     in
                                                  (match uu____5660 with
                                                   | (pre,post) ->
                                                       ((let uu____6181 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____6184 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____6187 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___695_6190
                                                             = ed  in
                                                           let uu____6191 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____6192 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____6193 =
                                                             let uu____6194 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____6194)
                                                              in
                                                           let uu____6201 =
                                                             let uu____6202 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____6202)
                                                              in
                                                           let uu____6209 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____6210 =
                                                             let uu____6211 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____6211)
                                                              in
                                                           let uu____6218 =
                                                             let uu____6219 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____6219)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____6191;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____6192;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____6193;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____6201;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____6209;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____6210;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____6218;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___695_6190.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____6226 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____6226
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____6244
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____6244
                                                               then
                                                                 let uu____6248
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____6248
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
                                                                    let uu____6268
                                                                    =
                                                                    let uu____6271
                                                                    =
                                                                    let uu____6272
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____6272)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6271
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
                                                                    uu____6268;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____6279
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____6279
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____6282
                                                                 =
                                                                 let uu____6285
                                                                   =
                                                                   let uu____6288
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____6288
                                                                    in
                                                                 FStar_List.append
                                                                   uu____6285
                                                                   sigelts'
                                                                  in
                                                               (uu____6282,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____6329 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6329 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6364 = FStar_List.hd ses  in
            uu____6364.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6369 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6375,[],t,uu____6377,uu____6378);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6380;
               FStar_Syntax_Syntax.sigattrs = uu____6381;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6383,_t_top,_lex_t_top,_6417,uu____6386);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6388;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6389;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6391,_t_cons,_lex_t_cons,_6425,uu____6394);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6396;
                 FStar_Syntax_Syntax.sigattrs = uu____6397;_}::[]
               when
               ((_6417 = Prims.int_zero) && (_6425 = Prims.int_zero)) &&
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
                 let uu____6450 =
                   let uu____6457 =
                     let uu____6458 =
                       let uu____6465 =
                         let uu____6468 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6468
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6465, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6458  in
                   FStar_Syntax_Syntax.mk uu____6457  in
                 uu____6450 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
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
                   let uu____6483 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6483
                    in
                 let hd1 =
                   let uu____6485 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6485
                    in
                 let tl1 =
                   let uu____6487 =
                     let uu____6488 =
                       let uu____6495 =
                         let uu____6496 =
                           let uu____6503 =
                             let uu____6506 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6506
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6503, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6496  in
                       FStar_Syntax_Syntax.mk uu____6495  in
                     uu____6488 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6487
                    in
                 let res =
                   let uu____6512 =
                     let uu____6519 =
                       let uu____6520 =
                         let uu____6527 =
                           let uu____6530 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6530
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6527,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6520  in
                     FStar_Syntax_Syntax.mk uu____6519  in
                   uu____6512 FStar_Pervasives_Native.None r2  in
                 let uu____6533 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6533
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
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____6572 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6572;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6577 ->
               let err_msg =
                 let uu____6582 =
                   let uu____6584 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6584  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6582
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
    fun uu____6609  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6609 with
          | (uvs,t) ->
              let uu____6622 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6622 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6634 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6634 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6652 =
                        let uu____6655 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____6655
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____6652)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6678 =
          let uu____6679 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6679 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6678 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6704 =
          let uu____6705 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6705 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6704 r
  
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          (let uu____6754 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____6754
           then
             let uu____6757 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6757
           else ());
          (let uu____6762 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____6762 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____6793 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____6793 FStar_List.flatten  in
               ((let uu____6807 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6810 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____6810)
                    in
                 if uu____6807
                 then ()
                 else
                   (let env1 =
                      FStar_TypeChecker_Env.push_sigelt env sig_bndle  in
                    FStar_List.iter
                      (fun ty  ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env1
                            in
                         if Prims.op_Negation b
                         then
                           let uu____6826 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____6836,uu____6837,uu____6838,uu____6839,uu____6840)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6849 -> failwith "Impossible!"  in
                           match uu____6826 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____6868 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____6878,uu____6879,ty_lid,uu____6881,uu____6882)
                               -> (data_lid, ty_lid)
                           | uu____6889 -> failwith "Impossible"  in
                         match uu____6868 with
                         | (data_lid,ty_lid) ->
                             let uu____6897 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____6900 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____6900)
                                in
                             if uu____6897
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____6914 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____6919,uu____6920,uu____6921,uu____6922,uu____6923)
                         -> lid
                     | uu____6932 -> failwith "Impossible"  in
                   FStar_List.existsb
                     (fun s  ->
                        s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                     FStar_TypeChecker_TcInductive.early_prims_inductives
                    in
                 let is_noeq =
                   FStar_List.existsb
                     (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                    in
                 let res =
                   let uu____6950 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____6950
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
                            sig_bndle tcs datas env
                        else
                          FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                            sig_bndle tcs datas env
                         in
                      (sig_bndle, (FStar_List.append ses1 data_ops_ses)))
                    in
                 res)))
  
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let pop1 uu____7025 =
            let uu____7026 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___873_7036  ->
               match () with
               | () ->
                   let uu____7043 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7043 (fun r  -> pop1 (); r)) ()
          with | uu___872_7074 -> (pop1 (); FStar_Exn.raise uu___872_7074)
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
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
      | uu____7390 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7448 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7448 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7473 .
    'Auu____7473 FStar_Pervasives_Native.option -> 'Auu____7473 Prims.list
  =
  fun uu___0_7482  ->
    match uu___0_7482 with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let (check_multi_eq :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1  ->
    fun l2  ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____7562 = collect1 tl1  in
            (match uu____7562 with
             | [] -> [(hd1, Prims.int_one)]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + Prims.int_one)) :: t
                 else (hd1, Prims.int_one) :: (h, n1) :: t)
         in
      let summ l = collect1 l  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],[]) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____7800,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____7856) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n1)
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2
         in
      aux l11 l21
  
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____8066 =
            let uu____8068 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8068  in
          if uu____8066
          then
            let uu____8071 =
              let uu____8076 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8077 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8076 uu____8077  in
            (match uu____8071 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some iface_decls1 ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb  ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                         let has_iface_val =
                           FStar_All.pipe_right iface_decls1
                             (FStar_Util.for_some
                                (FStar_Parser_AST.decl_is_val
                                   ((lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident))
                            in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef
                              in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr
                              in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu____8110 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8111 =
                                let uu____8117 =
                                  let uu____8119 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8121 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8119 uu____8121
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8117)
                                 in
                              FStar_Errors.log_issue uu____8110 uu____8111
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8128 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8129 =
                                   let uu____8135 =
                                     let uu____8137 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8137
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8135)
                                    in
                                 FStar_Errors.log_issue uu____8128 uu____8129)
                              else ())
                         else ())))
          else ()
      | uu____8147 -> ()
  
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun se  ->
      let env = env0  in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8192 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8220 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let ses1 =
             let uu____8280 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8280
             then
               let ses1 =
                 let uu____8288 =
                   let uu____8289 =
                     let uu____8290 =
                       tc_inductive
                         (let uu___1005_8299 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1005_8299.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1005_8299.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1005_8299.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1005_8299.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1005_8299.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1005_8299.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1005_8299.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1005_8299.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1005_8299.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1005_8299.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1005_8299.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1005_8299.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1005_8299.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1005_8299.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1005_8299.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1005_8299.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1005_8299.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1005_8299.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1005_8299.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1005_8299.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1005_8299.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1005_8299.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1005_8299.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1005_8299.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1005_8299.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1005_8299.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1005_8299.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1005_8299.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1005_8299.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1005_8299.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1005_8299.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1005_8299.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1005_8299.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1005_8299.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1005_8299.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1005_8299.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1005_8299.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1005_8299.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1005_8299.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1005_8299.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1005_8299.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1005_8299.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8290
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8289
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8288
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8313 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8313
                 then
                   let uu____8318 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1009_8322 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1009_8322.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1009_8322.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1009_8322.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1009_8322.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8318
                 else ());
                ses1)
             else ses  in
           let uu____8332 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8332 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1016_8356 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1016_8356.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1016_8356.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1016_8356.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1016_8356.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____8368 = cps_and_elaborate env ne  in
           (match uu____8368 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1030_8407 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1030_8407.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1030_8407.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1030_8407.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1030_8407.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1033_8409 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1033_8409.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1033_8409.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1033_8409.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1033_8409.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____8416 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____8416
             then
               let ne1 =
                 let uu____8420 =
                   let uu____8421 =
                     let uu____8422 =
                       tc_eff_decl
                         (let uu___1039_8425 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1039_8425.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1039_8425.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1039_8425.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1039_8425.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1039_8425.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1039_8425.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1039_8425.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1039_8425.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1039_8425.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1039_8425.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1039_8425.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1039_8425.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1039_8425.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1039_8425.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1039_8425.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1039_8425.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1039_8425.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1039_8425.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1039_8425.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1039_8425.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1039_8425.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1039_8425.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1039_8425.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1039_8425.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1039_8425.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1039_8425.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1039_8425.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1039_8425.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1039_8425.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1039_8425.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1039_8425.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1039_8425.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1039_8425.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1039_8425.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1039_8425.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1039_8425.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1039_8425.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1039_8425.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1039_8425.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1039_8425.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1039_8425.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1039_8425.FStar_TypeChecker_Env.strict_args_tab)
                          }) ne
                        in
                     FStar_All.pipe_right uu____8422
                       (fun ne1  ->
                          let uu___1042_8431 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1042_8431.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1042_8431.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1042_8431.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1042_8431.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____8421
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____8420
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____8433 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8433
                 then
                   let uu____8438 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1046_8442 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1046_8442.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1046_8442.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1046_8442.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1046_8442.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____8438
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env ne1  in
           let se1 =
             let uu___1051_8450 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___1051_8450.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___1051_8450.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___1051_8450.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___1051_8450.FStar_Syntax_Syntax.sigattrs)
             }  in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____8458 =
             let uu____8465 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8465
              in
           (match uu____8458 with
            | (a,wp_a_src) ->
                let uu____8482 =
                  let uu____8489 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8489
                   in
                (match uu____8482 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8507 =
                         let uu____8510 =
                           let uu____8511 =
                             let uu____8518 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8518)  in
                           FStar_Syntax_Syntax.NT uu____8511  in
                         [uu____8510]  in
                       FStar_Syntax_Subst.subst uu____8507 wp_b_tgt  in
                     let expected_k =
                       let uu____8526 =
                         let uu____8535 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8542 =
                           let uu____8551 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____8551]  in
                         uu____8535 :: uu____8542  in
                       let uu____8576 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8526 uu____8576  in
                     let repr_type eff_name a1 wp =
                       (let uu____8598 =
                          let uu____8600 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____8600  in
                        if uu____8598
                        then
                          let uu____8603 =
                            let uu____8609 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____8609)
                             in
                          let uu____8613 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____8603 uu____8613
                        else ());
                       (let uu____8616 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____8616 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr))
                               in
                            let uu____8653 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____8654 =
                              let uu____8661 =
                                let uu____8662 =
                                  let uu____8679 =
                                    let uu____8690 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____8699 =
                                      let uu____8710 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8710]  in
                                    uu____8690 :: uu____8699  in
                                  (repr, uu____8679)  in
                                FStar_Syntax_Syntax.Tm_app uu____8662  in
                              FStar_Syntax_Syntax.mk uu____8661  in
                            uu____8654 FStar_Pervasives_Native.None
                              uu____8653)
                        in
                     let uu____8755 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____8928 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____8939 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____8939 with
                               | (usubst,uvs1) ->
                                   let uu____8962 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____8963 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____8962, uu____8963)
                             else (env, lift_wp)  in
                           (match uu____8928 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9013 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9013))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9084 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____9099 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9099 with
                               | (usubst,uvs) ->
                                   let uu____9124 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9124)
                             else ([], lift)  in
                           (match uu____9084 with
                            | (uvs,lift1) ->
                                ((let uu____9160 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9160
                                  then
                                    let uu____9164 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9164
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9170 =
                                    let uu____9177 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9177 lift1
                                     in
                                  match uu____9170 with
                                  | (lift2,comp,uu____9202) ->
                                      let uu____9203 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9203 with
                                       | (uu____9232,lift_wp,lift_elab) ->
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
                                               Prims.int_zero
                                           then
                                             let uu____9264 =
                                               let uu____9275 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9275
                                                in
                                             let uu____9292 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9264, uu____9292)
                                           else
                                             (let uu____9321 =
                                                let uu____9332 =
                                                  let uu____9341 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9341)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9332
                                                 in
                                              let uu____9356 =
                                                let uu____9365 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9365)  in
                                              (uu____9321, uu____9356))))))
                        in
                     (match uu____8755 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1127_9439 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1127_9439.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1127_9439.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1127_9439.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1127_9439.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1127_9439.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1127_9439.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1127_9439.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1127_9439.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1127_9439.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1127_9439.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1127_9439.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1127_9439.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1127_9439.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1127_9439.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1127_9439.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1127_9439.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1127_9439.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1127_9439.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1127_9439.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1127_9439.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1127_9439.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1127_9439.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1127_9439.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1127_9439.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1127_9439.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1127_9439.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1127_9439.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1127_9439.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1127_9439.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1127_9439.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1127_9439.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1127_9439.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1127_9439.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1127_9439.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1127_9439.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1127_9439.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1127_9439.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1127_9439.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1127_9439.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1127_9439.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1127_9439.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1127_9439.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1127_9439.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9496 =
                                  let uu____9501 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9501 with
                                  | (usubst,uvs1) ->
                                      let uu____9524 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9525 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9524, uu____9525)
                                   in
                                (match uu____9496 with
                                 | (env2,lift2) ->
                                     let uu____9538 =
                                       let uu____9545 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9545
                                        in
                                     (match uu____9538 with
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
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp)
                                               in
                                            let lift_wp_a =
                                              let uu____9579 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9580 =
                                                let uu____9587 =
                                                  let uu____9588 =
                                                    let uu____9605 =
                                                      let uu____9616 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____9625 =
                                                        let uu____9636 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____9636]  in
                                                      uu____9616 ::
                                                        uu____9625
                                                       in
                                                    (lift_wp1, uu____9605)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9588
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9587
                                                 in
                                              uu____9580
                                                FStar_Pervasives_Native.None
                                                uu____9579
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____9684 =
                                              let uu____9693 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____9700 =
                                                let uu____9709 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____9716 =
                                                  let uu____9725 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____9725]  in
                                                uu____9709 :: uu____9716  in
                                              uu____9693 :: uu____9700  in
                                            let uu____9756 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____9684 uu____9756
                                             in
                                          let uu____9759 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____9759 with
                                           | (expected_k2,uu____9777,uu____9778)
                                               ->
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
                                                        expected_k2
                                                       in
                                                    let uu____9802 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____9802))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____9818 =
                              let uu____9820 =
                                let uu____9822 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9822
                                  FStar_List.length
                                 in
                              uu____9820 <> Prims.int_one  in
                            if uu____9818
                            then
                              let uu____9844 =
                                let uu____9850 =
                                  let uu____9852 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9854 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9856 =
                                    let uu____9858 =
                                      let uu____9860 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9860
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9858
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9852 uu____9854 uu____9856
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9850)
                                 in
                              FStar_Errors.raise_error uu____9844 r
                            else ());
                           (let uu____9887 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____9898 =
                                   let uu____9900 =
                                     let uu____9903 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____9903
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9900
                                     FStar_List.length
                                    in
                                 uu____9898 <> Prims.int_one)
                               in
                            if uu____9887
                            then
                              let uu____9957 =
                                let uu____9963 =
                                  let uu____9965 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9967 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9969 =
                                    let uu____9971 =
                                      let uu____9973 =
                                        let uu____9976 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____9976
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9973
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9971
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9965 uu____9967 uu____9969
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9963)
                                 in
                              FStar_Errors.raise_error uu____9957 r
                            else ());
                           (let sub2 =
                              let uu___1164_10035 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1164_10035.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1164_10035.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1167_10037 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1167_10037.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1167_10037.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1167_10037.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1167_10037.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____10051 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____10079 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10079 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10110 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10110 c  in
                    let uu____10119 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10119, uvs1, tps1, c1))
              in
           (match uu____10051 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10141 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10141 with
                 | (tps2,c2) ->
                     let uu____10158 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10158 with
                      | (tps3,env3,us) ->
                          let uu____10178 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10178 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10206)::uu____10207 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10226 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10234 =
                                   let uu____10236 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10236  in
                                 if uu____10234
                                 then
                                   let uu____10239 =
                                     let uu____10245 =
                                       let uu____10247 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10249 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10247 uu____10249
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10245)
                                      in
                                   FStar_Errors.raise_error uu____10239 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10257 =
                                   let uu____10258 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10258
                                    in
                                 match uu____10257 with
                                 | (uvs2,t) ->
                                     let uu____10289 =
                                       let uu____10294 =
                                         let uu____10307 =
                                           let uu____10308 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10308.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10307)  in
                                       match uu____10294 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10323,c5)) -> ([], c5)
                                       | (uu____10365,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10404 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10289 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____10438 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10438 with
                                              | (uu____10443,t1) ->
                                                  let uu____10445 =
                                                    let uu____10451 =
                                                      let uu____10453 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10455 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10459 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10453
                                                        uu____10455
                                                        uu____10459
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10451)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10445 r)
                                           else ();
                                           (let se1 =
                                              let uu___1237_10466 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1237_10466.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1237_10466.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1237_10466.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1237_10466.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10473,uu____10474,uu____10475) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10480  ->
                   match uu___1_10480 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10483 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10489,uu____10490) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_10499  ->
                   match uu___1_10499 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10502 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10513 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10513
             then
               let uu____10516 =
                 let uu____10522 =
                   let uu____10524 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10524
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10522)
                  in
               FStar_Errors.raise_error uu____10516 r
             else ());
            (let uu____10530 =
               let uu____10539 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10539
               then
                 let uu____10550 =
                   tc_declare_typ
                     (let uu___1261_10553 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1261_10553.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1261_10553.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1261_10553.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1261_10553.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1261_10553.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1261_10553.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1261_10553.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1261_10553.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1261_10553.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1261_10553.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1261_10553.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1261_10553.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1261_10553.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1261_10553.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1261_10553.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1261_10553.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1261_10553.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1261_10553.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1261_10553.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1261_10553.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1261_10553.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1261_10553.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1261_10553.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1261_10553.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1261_10553.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1261_10553.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1261_10553.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1261_10553.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1261_10553.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1261_10553.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1261_10553.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1261_10553.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1261_10553.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1261_10553.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1261_10553.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1261_10553.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1261_10553.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1261_10553.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1261_10553.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1261_10553.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1261_10553.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1261_10553.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1261_10553.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10550 with
                 | (uvs1,t1) ->
                     ((let uu____10578 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10578
                       then
                         let uu____10583 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10585 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10583 uu____10585
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10530 with
             | (uvs1,t1) ->
                 let uu____10620 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10620 with
                  | (uvs2,t2) ->
                      ([(let uu___1274_10650 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1274_10650.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1274_10650.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1274_10650.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1274_10650.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10655 =
             let uu____10664 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10664
             then
               let uu____10675 =
                 tc_assume
                   (let uu___1283_10678 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1283_10678.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1283_10678.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1283_10678.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1283_10678.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1283_10678.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1283_10678.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1283_10678.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1283_10678.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1283_10678.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1283_10678.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1283_10678.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1283_10678.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1283_10678.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1283_10678.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1283_10678.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1283_10678.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1283_10678.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1283_10678.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1283_10678.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1283_10678.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1283_10678.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1283_10678.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1283_10678.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1283_10678.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1283_10678.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1283_10678.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1283_10678.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1283_10678.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1283_10678.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1283_10678.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1283_10678.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1283_10678.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1283_10678.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1283_10678.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1283_10678.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1283_10678.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1283_10678.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1283_10678.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1283_10678.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1283_10678.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1283_10678.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1283_10678.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____10675 with
               | (uvs1,t1) ->
                   ((let uu____10704 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____10704
                     then
                       let uu____10709 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10711 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____10709
                         uu____10711
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10655 with
            | (uvs1,t1) ->
                let uu____10746 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____10746 with
                 | (uvs2,t2) ->
                     ([(let uu___1296_10776 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1296_10776.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1296_10776.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1296_10776.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1296_10776.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____10780 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____10780 with
            | (e1,c,g1) ->
                let uu____10800 =
                  let uu____10807 =
                    let uu____10810 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____10810  in
                  let uu____10811 =
                    let uu____10816 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____10816)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____10807 uu____10811
                   in
                (match uu____10800 with
                 | (e2,uu____10828,g) ->
                     ((let uu____10831 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____10831);
                      (let se1 =
                         let uu___1311_10833 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1311_10833.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1311_10833.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1311_10833.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1311_10833.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____10845 = FStar_Options.debug_any ()  in
             if uu____10845
             then
               let uu____10848 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____10850 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____10848
                 uu____10850
             else ());
            (let uu____10855 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____10855 with
             | (t1,uu____10873,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____10887 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____10887 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____10890 =
                              let uu____10896 =
                                let uu____10898 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____10900 =
                                  let uu____10902 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____10902
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____10898 uu____10900
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____10896)
                               in
                            FStar_Errors.raise_error uu____10890 r
                        | uu____10914 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1332_10919 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1332_10919.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1332_10919.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1332_10919.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1332_10919.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1332_10919.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1332_10919.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1332_10919.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1332_10919.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1332_10919.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1332_10919.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1332_10919.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1332_10919.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1332_10919.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1332_10919.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1332_10919.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1332_10919.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1332_10919.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1332_10919.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1332_10919.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1332_10919.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1332_10919.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1332_10919.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1332_10919.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1332_10919.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1332_10919.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1332_10919.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1332_10919.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1332_10919.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1332_10919.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1332_10919.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1332_10919.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1332_10919.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1332_10919.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1332_10919.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1332_10919.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1332_10919.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1332_10919.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1332_10919.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1332_10919.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1332_10919.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1332_10919.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1332_10919.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1332_10919.FStar_TypeChecker_Env.strict_args_tab)
                      }  in
                    ([], ses, env1))))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let check_quals_eq l qopt val_q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some val_q
             | FStar_Pervasives_Native.Some q' ->
                 let drop_logic =
                   FStar_List.filter
                     (fun x  ->
                        Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                    in
                 let uu____10987 =
                   let uu____10989 =
                     let uu____10998 = drop_logic val_q  in
                     let uu____11001 = drop_logic q'  in
                     (uu____10998, uu____11001)  in
                   match uu____10989 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____10987
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11028 =
                      let uu____11034 =
                        let uu____11036 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11038 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11040 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11036 uu____11038 uu____11040
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11034)
                       in
                    FStar_Errors.raise_error uu____11028 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11077 =
                   let uu____11078 = FStar_Syntax_Subst.compress def  in
                   uu____11078.FStar_Syntax_Syntax.n  in
                 match uu____11077 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11090,uu____11091) -> binders
                 | uu____11116 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11128;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11233) -> val_bs1
                     | (uu____11264,[]) -> val_bs1
                     | ((body_bv,uu____11296)::bt,(val_bv,aqual)::vt) ->
                         let uu____11353 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11377) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1401_11391 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1403_11394 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1403_11394.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1401_11391.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1401_11391.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11353
                      in
                   let uu____11401 =
                     let uu____11408 =
                       let uu____11409 =
                         let uu____11424 = rename_binders1 def_bs val_bs  in
                         (uu____11424, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11409  in
                     FStar_Syntax_Syntax.mk uu____11408  in
                   uu____11401 FStar_Pervasives_Native.None r1
               | uu____11443 -> typ1  in
             let uu___1409_11444 = lb  in
             let uu____11445 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11445;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1409_11444.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11448 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11503  ->
                     fun lb  ->
                       match uu____11503 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11549 =
                             let uu____11561 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11561 with
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
                                   | uu____11641 ->
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
                                  (let uu____11688 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____11688, quals_opt1)))
                              in
                           (match uu____11549 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11448 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____11792 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_11798  ->
                                match uu___2_11798 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____11803 -> false))
                         in
                      if uu____11792
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____11816 =
                    let uu____11823 =
                      let uu____11824 =
                        let uu____11838 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____11838)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____11824  in
                    FStar_Syntax_Syntax.mk uu____11823  in
                  uu____11816 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1452_11857 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1452_11857.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1452_11857.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1452_11857.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1452_11857.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1452_11857.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1452_11857.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1452_11857.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1452_11857.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1452_11857.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1452_11857.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1452_11857.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1452_11857.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1452_11857.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1452_11857.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1452_11857.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1452_11857.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1452_11857.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1452_11857.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1452_11857.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1452_11857.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1452_11857.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1452_11857.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1452_11857.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1452_11857.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1452_11857.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1452_11857.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1452_11857.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1452_11857.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1452_11857.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1452_11857.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1452_11857.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1452_11857.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1452_11857.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1452_11857.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1452_11857.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1452_11857.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1452_11857.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1452_11857.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1452_11857.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1452_11857.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1452_11857.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1452_11857.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____11860 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____11860
                  then
                    let drop_lbtyp e_lax =
                      let uu____11869 =
                        let uu____11870 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____11870.FStar_Syntax_Syntax.n  in
                      match uu____11869 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____11892 =
                              let uu____11893 = FStar_Syntax_Subst.compress e
                                 in
                              uu____11893.FStar_Syntax_Syntax.n  in
                            match uu____11892 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____11897,lb1::[]),uu____11899) ->
                                let uu____11915 =
                                  let uu____11916 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____11916.FStar_Syntax_Syntax.n  in
                                (match uu____11915 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____11921 -> false)
                            | uu____11923 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1477_11927 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1479_11942 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1479_11942.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1477_11927.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1477_11927.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____11945 -> e_lax  in
                    let uu____11946 =
                      FStar_Util.record_time
                        (fun uu____11954  ->
                           let uu____11955 =
                             let uu____11956 =
                               let uu____11957 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1483_11966 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1483_11966.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1483_11966.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1483_11966.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1483_11966.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1483_11966.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1483_11966.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1483_11966.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1483_11966.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1483_11966.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1483_11966.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1483_11966.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1483_11966.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1483_11966.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1483_11966.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1483_11966.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1483_11966.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1483_11966.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1483_11966.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1483_11966.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1483_11966.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1483_11966.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1483_11966.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1483_11966.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1483_11966.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1483_11966.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1483_11966.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1483_11966.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1483_11966.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1483_11966.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1483_11966.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1483_11966.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1483_11966.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1483_11966.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1483_11966.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1483_11966.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1483_11966.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1483_11966.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1483_11966.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1483_11966.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1483_11966.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1483_11966.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1483_11966.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____11957
                                 (fun uu____11979  ->
                                    match uu____11979 with
                                    | (e1,uu____11987,uu____11988) -> e1)
                                in
                             FStar_All.pipe_right uu____11956
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____11955 drop_lbtyp)
                       in
                    match uu____11946 with
                    | (e1,ms) ->
                        ((let uu____11994 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____11994
                          then
                            let uu____11999 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____11999
                          else ());
                         (let uu____12005 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____12005
                          then
                            let uu____12010 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____12010
                          else ());
                         e1)
                  else e  in
                let uu____12017 =
                  let uu____12026 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12026 with
                  | FStar_Pervasives_Native.None  ->
                      ((se.FStar_Syntax_Syntax.sigattrs),
                        FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                      (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats,args) ->
                      (FStar_Errors.log_issue r
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_with`");
                       ((se.FStar_Syntax_Syntax.sigattrs),
                         FStar_Pervasives_Native.None))
                   in
                (match uu____12017 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1513_12131 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1513_12131.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1513_12131.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1513_12131.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1513_12131.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1520_12144 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1520_12144.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12145 =
                       FStar_Util.record_time
                         (fun uu____12164  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____12145 with
                      | (r1,ms) ->
                          ((let uu____12192 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____12192
                            then
                              let uu____12197 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____12197
                            else ());
                           (let uu____12202 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____12227;
                                   FStar_Syntax_Syntax.vars = uu____12228;_},uu____12229,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____12259 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____12259)
                                     in
                                  let lbs3 =
                                    let uu____12283 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____12283)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____12306,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____12311 -> quals  in
                                  ((let uu___1550_12320 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1550_12320.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1550_12320.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1550_12320.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____12323 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____12202 with
                            | (se2,lbs1) ->
                                (FStar_All.pipe_right
                                   (FStar_Pervasives_Native.snd lbs1)
                                   (FStar_List.iter
                                      (fun lb  ->
                                         let fv =
                                           FStar_Util.right
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_TypeChecker_Env.insert_fv_info
                                           env1 fv
                                           lb.FStar_Syntax_Syntax.lbtyp));
                                 (let uu____12379 = log env1  in
                                  if uu____12379
                                  then
                                    let uu____12382 =
                                      let uu____12384 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____12404 =
                                                    let uu____12413 =
                                                      let uu____12414 =
                                                        let uu____12417 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____12417.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____12414.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____12413
                                                     in
                                                  match uu____12404 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____12426 -> false  in
                                                if should_log
                                                then
                                                  let uu____12438 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____12440 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____12438
                                                    uu____12440
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____12384
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____12382
                                  else ());
                                 check_must_erase_attribute env0 se2;
                                 ([se2], [], env0))))))))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____12492 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12492
       then
         let uu____12495 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12495
       else ());
      (let uu____12500 = get_fail_se se  in
       match uu____12500 with
       | FStar_Pervasives_Native.Some (uu____12521,false ) when
           let uu____12538 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12538 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1581_12564 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1581_12564.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1581_12564.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1581_12564.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1581_12564.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1581_12564.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1581_12564.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1581_12564.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1581_12564.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1581_12564.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1581_12564.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1581_12564.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1581_12564.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1581_12564.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1581_12564.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1581_12564.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1581_12564.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1581_12564.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1581_12564.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1581_12564.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1581_12564.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1581_12564.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1581_12564.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1581_12564.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1581_12564.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1581_12564.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1581_12564.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1581_12564.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1581_12564.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1581_12564.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1581_12564.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1581_12564.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1581_12564.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1581_12564.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1581_12564.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1581_12564.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1581_12564.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1581_12564.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1581_12564.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1581_12564.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1581_12564.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1581_12564.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1581_12564.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1581_12564.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____12569 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12569
             then
               let uu____12572 =
                 let uu____12574 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12574
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12572
             else ());
            (let uu____12588 =
               FStar_Errors.catch_errors
                 (fun uu____12618  ->
                    FStar_Options.with_saved_options
                      (fun uu____12630  -> tc_decl' env' se))
                in
             match uu____12588 with
             | (errs,uu____12642) ->
                 ((let uu____12672 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12672
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12707 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12707  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12719 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12730 =
                            let uu____12740 = check_multi_eq errnos1 actual
                               in
                            match uu____12740 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____12730 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____12805 =
                                   let uu____12811 =
                                     let uu____12813 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____12816 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____12819 =
                                       FStar_Util.string_of_int e  in
                                     let uu____12821 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____12823 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____12813 uu____12816 uu____12819
                                       uu____12821 uu____12823
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____12811)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12805)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____12850 .
    'Auu____12850 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env  ->
    fun hidden  ->
      fun se  ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___3_12893  ->
                  match uu___3_12893 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____12896 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____12907) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____12915 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____12925 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____12930 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____12946 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____12972 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12998) ->
            let uu____13007 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13007
            then
              let for_export_bundle se1 uu____13044 =
                match uu____13044 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13083,uu____13084) ->
                         let dec =
                           let uu___1657_13094 = se1  in
                           let uu____13095 =
                             let uu____13096 =
                               let uu____13103 =
                                 let uu____13104 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13104  in
                               (l, us, uu____13103)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13096
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13095;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1657_13094.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1657_13094.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1657_13094.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13114,uu____13115,uu____13116) ->
                         let dec =
                           let uu___1668_13124 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1668_13124.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1668_13124.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1668_13124.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13129 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13152,uu____13153,uu____13154) ->
            let uu____13155 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13155 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13179 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13179
            then
              ([(let uu___1684_13198 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1684_13198.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1684_13198.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1684_13198.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13201 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_13207  ->
                         match uu___4_13207 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13210 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13216 ->
                             true
                         | uu____13218 -> false))
                  in
               if uu____13201 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13239 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13244 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13249 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13254 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13259 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13277) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13291 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13291
            then ([], hidden)
            else
              (let dec =
                 let uu____13312 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13312;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13323 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13323
            then
              let uu____13334 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1721_13348 = se  in
                        let uu____13349 =
                          let uu____13350 =
                            let uu____13357 =
                              let uu____13358 =
                                let uu____13361 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13361.FStar_Syntax_Syntax.fv_name  in
                              uu____13358.FStar_Syntax_Syntax.v  in
                            (uu____13357, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13350  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13349;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1721_13348.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1721_13348.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1721_13348.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13334, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13384 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13384
       then
         let uu____13387 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13387
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13392 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13410 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____13427) ->
           let env1 =
             let uu___1742_13432 = env  in
             let uu____13433 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1742_13432.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1742_13432.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1742_13432.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1742_13432.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1742_13432.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1742_13432.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1742_13432.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1742_13432.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1742_13432.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1742_13432.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1742_13432.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1742_13432.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1742_13432.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1742_13432.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1742_13432.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1742_13432.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1742_13432.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1742_13432.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1742_13432.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1742_13432.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1742_13432.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1742_13432.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1742_13432.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1742_13432.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1742_13432.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1742_13432.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1742_13432.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1742_13432.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1742_13432.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1742_13432.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1742_13432.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1742_13432.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1742_13432.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1742_13432.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13433;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1742_13432.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1742_13432.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1742_13432.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1742_13432.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1742_13432.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1742_13432.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1742_13432.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1742_13432.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1742_13432.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1742_13435 = env  in
             let uu____13436 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1742_13435.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1742_13435.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1742_13435.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1742_13435.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1742_13435.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1742_13435.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1742_13435.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1742_13435.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1742_13435.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1742_13435.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1742_13435.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1742_13435.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1742_13435.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1742_13435.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1742_13435.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1742_13435.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1742_13435.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1742_13435.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1742_13435.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1742_13435.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1742_13435.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1742_13435.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1742_13435.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1742_13435.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1742_13435.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1742_13435.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1742_13435.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1742_13435.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1742_13435.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1742_13435.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1742_13435.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1742_13435.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1742_13435.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1742_13435.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13436;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1742_13435.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1742_13435.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1742_13435.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1742_13435.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1742_13435.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1742_13435.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1742_13435.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1742_13435.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1742_13435.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____13437) ->
           let env1 =
             let uu___1742_13440 = env  in
             let uu____13441 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1742_13440.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1742_13440.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1742_13440.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1742_13440.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1742_13440.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1742_13440.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1742_13440.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1742_13440.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1742_13440.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1742_13440.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1742_13440.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1742_13440.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1742_13440.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1742_13440.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1742_13440.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1742_13440.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1742_13440.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1742_13440.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1742_13440.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1742_13440.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1742_13440.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1742_13440.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1742_13440.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1742_13440.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1742_13440.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1742_13440.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1742_13440.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1742_13440.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1742_13440.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1742_13440.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1742_13440.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1742_13440.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1742_13440.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1742_13440.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13441;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1742_13440.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1742_13440.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1742_13440.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1742_13440.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1742_13440.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1742_13440.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1742_13440.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1742_13440.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1742_13440.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13442) ->
           let env1 =
             let uu___1742_13447 = env  in
             let uu____13448 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1742_13447.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1742_13447.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1742_13447.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1742_13447.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1742_13447.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1742_13447.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1742_13447.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1742_13447.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1742_13447.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1742_13447.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1742_13447.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1742_13447.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1742_13447.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1742_13447.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1742_13447.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1742_13447.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1742_13447.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1742_13447.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1742_13447.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1742_13447.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1742_13447.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1742_13447.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1742_13447.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1742_13447.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1742_13447.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1742_13447.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1742_13447.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1742_13447.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1742_13447.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1742_13447.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1742_13447.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1742_13447.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1742_13447.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1742_13447.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____13448;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1742_13447.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1742_13447.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1742_13447.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1742_13447.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1742_13447.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1742_13447.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1742_13447.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1742_13447.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1742_13447.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____13450 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13451 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13461 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13461) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13462,uu____13463,uu____13464) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13469  ->
                   match uu___5_13469 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13472 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13474,uu____13475) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_13484  ->
                   match uu___5_13484 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13487 -> false))
           -> env
       | uu____13489 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13558 se =
        match uu____13558 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13611 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13611
              then
                let uu____13614 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13614
              else ());
             (let uu____13619 = tc_decl env1 se  in
              match uu____13619 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13672 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13672
                             then
                               let uu____13676 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13676
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13692 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13692
                             then
                               let uu____13696 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13696
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  (FStar_TypeChecker_Env.promote_id_info env2
                     (fun t  ->
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
                           (fun env3  ->
                              fun se1  -> add_sigelt_to_env env3 se1) env2)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____13713 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13713
                     then
                       let uu____13718 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13727 =
                                  let uu____13729 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____13729 "\n"  in
                                Prims.op_Hat s uu____13727) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13718
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13739 =
                       let uu____13748 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13748
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____13790 se1 =
                            match uu____13790 with
                            | (exports1,hidden1) ->
                                let uu____13818 = for_export env3 hidden1 se1
                                   in
                                (match uu____13818 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13739 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____13972 = acc  in
        match uu____13972 with
        | (uu____14007,uu____14008,env1,uu____14010) ->
            let uu____14023 =
              FStar_Util.record_time
                (fun uu____14070  -> process_one_decl acc se)
               in
            (match uu____14023 with
             | (r,ms_elapsed) ->
                 ((let uu____14136 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14136
                   then
                     let uu____14140 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14142 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14140 uu____14142
                   else ());
                  r))
         in
      let uu____14147 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14147 with
      | (ses1,exports,env1,uu____14195) ->
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
          let uu___1839_14233 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1839_14233.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1839_14233.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1839_14233.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1839_14233.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1839_14233.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1839_14233.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1839_14233.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1839_14233.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1839_14233.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1839_14233.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___1839_14233.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1839_14233.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1839_14233.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1839_14233.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1839_14233.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1839_14233.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1839_14233.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___1839_14233.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1839_14233.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1839_14233.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1839_14233.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1839_14233.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1839_14233.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1839_14233.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1839_14233.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1839_14233.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1839_14233.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1839_14233.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1839_14233.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1839_14233.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1839_14233.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1839_14233.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1839_14233.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1839_14233.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___1839_14233.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___1839_14233.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1839_14233.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1839_14233.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1839_14233.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1839_14233.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1839_14233.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____14253 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14253 with
          | (univs2,t1) ->
              ((let uu____14261 =
                  let uu____14263 =
                    let uu____14269 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14269  in
                  FStar_All.pipe_left uu____14263
                    (FStar_Options.Other "Exports")
                   in
                if uu____14261
                then
                  let uu____14273 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14275 =
                    let uu____14277 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14277
                      (FStar_String.concat ", ")
                     in
                  let uu____14294 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14273 uu____14275 uu____14294
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14300 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14300 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14326 =
             let uu____14328 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14330 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14328 uu____14330
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14326);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14341) ->
              let uu____14350 =
                let uu____14352 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14352  in
              if uu____14350
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14366,uu____14367) ->
              let t =
                let uu____14379 =
                  let uu____14386 =
                    let uu____14387 =
                      let uu____14402 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14402)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14387  in
                  FStar_Syntax_Syntax.mk uu____14386  in
                uu____14379 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14418,uu____14419,uu____14420) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14430 =
                let uu____14432 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14432  in
              if uu____14430 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14440,lbs),uu____14442) ->
              let uu____14453 =
                let uu____14455 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14455  in
              if uu____14453
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
              let uu____14478 =
                let uu____14480 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14480  in
              if uu____14478
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14501 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14502 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14509 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14510 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14511 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14512 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14519 -> ()  in
        let uu____14520 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14520 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14626) -> true
             | uu____14628 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14658 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14697 ->
                   let uu____14698 =
                     let uu____14705 =
                       let uu____14706 =
                         let uu____14721 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14721)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14706  in
                     FStar_Syntax_Syntax.mk uu____14705  in
                   uu____14698 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14738,uu____14739) ->
            let s1 =
              let uu___1965_14749 = s  in
              let uu____14750 =
                let uu____14751 =
                  let uu____14758 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14758)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14751  in
              let uu____14759 =
                let uu____14762 =
                  let uu____14765 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14765  in
                FStar_Syntax_Syntax.Assumption :: uu____14762  in
              {
                FStar_Syntax_Syntax.sigel = uu____14750;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1965_14749.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14759;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1965_14749.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1965_14749.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____14768 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____14793 lbdef =
        match uu____14793 with
        | (uvs,t) ->
            let attrs =
              let uu____14804 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____14804
              then
                let uu____14809 =
                  let uu____14810 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____14810
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____14809 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___1978_14813 = s  in
            let uu____14814 =
              let uu____14817 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____14817  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1978_14813.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14814;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1978_14813.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____14835 -> failwith "Impossible!"  in
        let c_opt =
          let uu____14842 = FStar_Syntax_Util.is_unit t  in
          if uu____14842
          then
            let uu____14849 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____14849
          else
            (let uu____14856 =
               let uu____14857 = FStar_Syntax_Subst.compress t  in
               uu____14857.FStar_Syntax_Syntax.n  in
             match uu____14856 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____14864,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____14888 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____14900 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____14900
            then false
            else
              (let uu____14907 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____14907
               then true
               else
                 (let uu____14914 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____14914))
         in
      let extract_sigelt s =
        (let uu____14926 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____14926
         then
           let uu____14929 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____14929
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____14936 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____14956 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____14975 ->
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
                             (lid,uu____15021,uu____15022,uu____15023,uu____15024,uu____15025)
                             ->
                             ((let uu____15035 =
                                 let uu____15038 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15038  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15035);
                              (let uu____15087 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15087 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15091,uu____15092,uu____15093,uu____15094,uu____15095)
                             ->
                             ((let uu____15103 =
                                 let uu____15106 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15106  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15103);
                              sigelts1)
                         | uu____15155 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15164 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15164
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15174 =
                    let uu___2042_15175 = s  in
                    let uu____15176 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2042_15175.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2042_15175.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15176;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2042_15175.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2042_15175.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15174])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15187 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15187
             then []
             else
               (let uu____15194 = lbs  in
                match uu____15194 with
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
                        (fun uu____15256  ->
                           match uu____15256 with
                           | (uu____15264,t,uu____15266) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15283  ->
                             match uu____15283 with
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
                           (fun uu____15310  ->
                              match uu____15310 with
                              | (uu____15318,t,uu____15320) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15332,uu____15333) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15341 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15370 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15370) uu____15341
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15374 =
                    let uu___2084_15375 = s  in
                    let uu____15376 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2084_15375.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2084_15375.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15376;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2084_15375.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2084_15375.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15374]
                else [])
             else
               (let uu____15383 =
                  let uu___2086_15384 = s  in
                  let uu____15385 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2086_15384.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2086_15384.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15385;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2086_15384.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2086_15384.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15383])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15388 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15389 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15390 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15391 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15404 -> [s])
         in
      let uu___2098_15405 = m  in
      let uu____15406 =
        let uu____15407 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15407 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2098_15405.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15406;
        FStar_Syntax_Syntax.exports =
          (uu___2098_15405.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15458  -> FStar_TypeChecker_Env.snapshot env msg)
  
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15505  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15520 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15520
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
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
      (let uu____15609 = FStar_Options.debug_any ()  in
       if uu____15609
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
         let uu___2123_15625 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2123_15625.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2123_15625.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2123_15625.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2123_15625.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2123_15625.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2123_15625.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2123_15625.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2123_15625.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2123_15625.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2123_15625.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2123_15625.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2123_15625.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2123_15625.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2123_15625.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2123_15625.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2123_15625.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2123_15625.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2123_15625.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2123_15625.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2123_15625.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2123_15625.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2123_15625.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2123_15625.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2123_15625.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2123_15625.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2123_15625.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2123_15625.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2123_15625.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2123_15625.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2123_15625.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2123_15625.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2123_15625.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2123_15625.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2123_15625.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2123_15625.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2123_15625.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2123_15625.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2123_15625.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2123_15625.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2123_15625.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2123_15625.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2123_15625.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15627 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15627 with
       | (ses,exports,env3) ->
           ((let uu___2131_15660 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2131_15660.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2131_15660.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2131_15660.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____15689 = tc_decls env decls  in
        match uu____15689 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2140_15720 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2140_15720.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2140_15720.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2140_15720.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun m  ->
      fun iface_exists  ->
        let msg =
          Prims.op_Hat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let env01 = push_context env0 msg  in
        let uu____15781 = tc_partial_modul env01 m  in
        match uu____15781 with
        | (modul,non_private_decls,env) ->
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
                (let uu____15818 = FStar_Errors.get_err_count ()  in
                 uu____15818 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____15829 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____15829
                then
                  let uu____15833 =
                    let uu____15835 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15835 then "" else " (in lax mode) "  in
                  let uu____15843 =
                    let uu____15845 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15845
                    then
                      let uu____15849 =
                        let uu____15851 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____15851 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____15849
                    else ""  in
                  let uu____15858 =
                    let uu____15860 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15860
                    then
                      let uu____15864 =
                        let uu____15866 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____15866 "\n"  in
                      Prims.op_Hat "\nto: " uu____15864
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15833
                    uu____15843 uu____15858
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2166_15880 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2166_15880.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2166_15880.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2166_15880.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2166_15880.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2166_15880.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2166_15880.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2166_15880.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2166_15880.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2166_15880.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2166_15880.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2166_15880.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2166_15880.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2166_15880.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2166_15880.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2166_15880.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2166_15880.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2166_15880.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2166_15880.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2166_15880.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2166_15880.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2166_15880.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2166_15880.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2166_15880.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2166_15880.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2166_15880.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2166_15880.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2166_15880.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2166_15880.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2166_15880.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2166_15880.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2166_15880.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2166_15880.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2166_15880.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2166_15880.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2166_15880.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2166_15880.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2166_15880.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2166_15880.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2166_15880.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2166_15880.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2166_15880.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2166_15880.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2166_15880.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2169_15882 = en01  in
                    let uu____15883 =
                      let uu____15898 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____15898, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2169_15882.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2169_15882.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2169_15882.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2169_15882.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2169_15882.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2169_15882.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2169_15882.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2169_15882.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2169_15882.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2169_15882.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2169_15882.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2169_15882.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2169_15882.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2169_15882.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2169_15882.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2169_15882.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2169_15882.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2169_15882.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2169_15882.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2169_15882.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2169_15882.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2169_15882.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2169_15882.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2169_15882.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2169_15882.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2169_15882.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2169_15882.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2169_15882.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2169_15882.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2169_15882.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2169_15882.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____15883;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2169_15882.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2169_15882.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2169_15882.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2169_15882.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2169_15882.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2169_15882.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2169_15882.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2169_15882.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2169_15882.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2169_15882.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2169_15882.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2169_15882.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____15944 =
                    let uu____15946 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____15946  in
                  if uu____15944
                  then
                    ((let uu____15950 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____15950 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____15954 = tc_modul en0 modul_iface true  in
                match uu____15954 with
                | (modul_iface1,env) ->
                    ((let uu___2178_15967 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2178_15967.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2178_15967.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2178_15967.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2180_15971 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2180_15971.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2180_15971.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2180_15971.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____15974 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____15974 FStar_Util.smap_clear);
               (let uu____16010 =
                  ((let uu____16014 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16014) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16017 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16017)
                   in
                if uu____16010 then check_exports env modul exports else ());
               (let uu____16023 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16023 (fun a4  -> ()));
               (modul, env))

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
        let uu____16038 =
          let uu____16040 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____16040  in
        push_context env uu____16038  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16061 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16072 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16072 with | (uu____16079,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16104 = FStar_Options.debug_any ()  in
         if uu____16104
         then
           let uu____16107 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16107
         else ());
        (let uu____16119 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16119
         then
           let uu____16122 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16122
         else ());
        (let env1 =
           let uu___2210_16128 = env  in
           let uu____16129 =
             let uu____16131 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16131  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2210_16128.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2210_16128.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2210_16128.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2210_16128.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2210_16128.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2210_16128.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2210_16128.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2210_16128.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2210_16128.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2210_16128.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2210_16128.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2210_16128.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2210_16128.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2210_16128.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2210_16128.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2210_16128.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2210_16128.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2210_16128.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2210_16128.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2210_16128.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16129;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2210_16128.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2210_16128.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2210_16128.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2210_16128.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2210_16128.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2210_16128.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2210_16128.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2210_16128.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2210_16128.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2210_16128.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2210_16128.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2210_16128.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2210_16128.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2210_16128.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2210_16128.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2210_16128.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2210_16128.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2210_16128.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2210_16128.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2210_16128.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2210_16128.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2210_16128.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2210_16128.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____16133 = tc_modul env1 m b  in
         match uu____16133 with
         | (m1,env2) ->
             ((let uu____16145 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16145
               then
                 let uu____16148 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16148
               else ());
              (let uu____16154 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16154
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses]
                          in
                       let update lb =
                         let uu____16192 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16192 with
                         | (univnames1,e) ->
                             let uu___2232_16199 = lb  in
                             let uu____16200 =
                               let uu____16203 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16203 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16200;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2232_16199.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2234_16204 = se  in
                       let uu____16205 =
                         let uu____16206 =
                           let uu____16213 =
                             let uu____16214 = FStar_List.map update lbs  in
                             (b1, uu____16214)  in
                           (uu____16213, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16206  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16205;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2234_16204.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2234_16204.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2234_16204.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2234_16204.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16222 -> se  in
                 let normalized_module =
                   let uu___2238_16224 = m1  in
                   let uu____16225 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2238_16224.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16225;
                     FStar_Syntax_Syntax.exports =
                       (uu___2238_16224.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2238_16224.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16226 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16226
               else ());
              (m1, env2)))
  