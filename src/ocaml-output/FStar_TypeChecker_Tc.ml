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
      let uu____47 = FStar_Options.reuse_hint_for ()  in
      match uu____47 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____52 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____52 l  in
          let uu___63_53 = env  in
          let uu____54 =
            let uu____67 =
              let uu____74 = let uu____79 = get_n lid  in (lid, uu____79)  in
              FStar_Pervasives_Native.Some uu____74  in
            (tbl, uu____67)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___63_53.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___63_53.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___63_53.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___63_53.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___63_53.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___63_53.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___63_53.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___63_53.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___63_53.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___63_53.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___63_53.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___63_53.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___63_53.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___63_53.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___63_53.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___63_53.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___63_53.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___63_53.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___63_53.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___63_53.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___63_53.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___63_53.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___63_53.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___63_53.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___63_53.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___63_53.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___63_53.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____54;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___63_53.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___63_53.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___63_53.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___63_53.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___63_53.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___63_53.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___63_53.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___63_53.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___63_53.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____96 = FStar_TypeChecker_Env.current_module env  in
                let uu____97 =
                  let uu____98 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____98 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____96 uu____97
            | l::uu____100 -> l  in
          let uu___64_103 = env  in
          let uu____104 =
            let uu____117 =
              let uu____124 = let uu____129 = get_n lid  in (lid, uu____129)
                 in
              FStar_Pervasives_Native.Some uu____124  in
            (tbl, uu____117)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___64_103.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___64_103.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___64_103.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___64_103.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___64_103.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___64_103.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___64_103.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___64_103.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___64_103.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___64_103.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___64_103.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___64_103.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___64_103.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___64_103.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___64_103.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___64_103.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___64_103.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___64_103.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___64_103.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___64_103.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___64_103.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___64_103.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___64_103.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___64_103.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___64_103.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___64_103.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___64_103.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____104;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___64_103.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___64_103.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___64_103.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___64_103.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___64_103.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___64_103.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___64_103.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___64_103.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___64_103.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____148 =
         let uu____149 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____149  in
       Prims.op_Negation uu____148)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____165 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____165 with
        | (t1,c,g) ->
            let uu____175 = FStar_TypeChecker_Rel.force_trivial_guard env g
               in
            t1
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        let uu____191 =
          let uu____192 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
          if uu____192
          then
            let uu____193 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.print2
              "Term has been %s-transformed to:\n%s\n----------\n" s
              uu____193
          else ()  in
        let uu____195 = FStar_TypeChecker_TcTerm.tc_term env t  in
        match uu____195 with
        | (t',uu____203,uu____204) ->
            let uu____205 =
              let uu____206 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____206
              then
                let uu____207 = FStar_Syntax_Print.term_to_string t'  in
                FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                  uu____207
              else ()  in
            t
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____224 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____224
  
let check_nogen :
  'Auu____233 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____233 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____256 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____256)
  
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
        let fail1 uu____290 =
          let uu____291 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____296 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____291 uu____296  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____336)::(wp,uu____338)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____353 -> fail1 ())
        | uu____354 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____365 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____365 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____393 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____393 t  in
          let open_univs_binders n_binders bs =
            let uu____405 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____405 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____413 =
            let uu____420 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____421 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____420 uu____421  in
          (match uu____413 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____432 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____432 with
                | (effect_params,env1,uu____441) ->
                    let uu____442 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____442 with
                     | (signature,uu____448) ->
                         let ed1 =
                           let uu___65_450 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___65_450.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___65_450.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___65_450.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___65_450.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___65_450.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___65_450.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___65_450.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___65_450.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___65_450.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___65_450.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___65_450.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___65_450.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___65_450.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___65_450.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___65_450.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___65_450.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___65_450.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___65_450.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____466 ->
                               let op uu____489 =
                                 match uu____489 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____509 =
                                       let uu____510 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____519 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____510
                                         uu____519
                                        in
                                     (us, uu____509)
                                  in
                               let uu___66_528 = ed1  in
                               let uu____529 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____530 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____531 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____532 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____533 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____534 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____535 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____536 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____537 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____538 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____539 =
                                 let uu____540 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____540  in
                               let uu____551 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____552 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____553 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___67_561 = a  in
                                      let uu____562 =
                                        let uu____563 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____563
                                         in
                                      let uu____572 =
                                        let uu____573 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____573
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___67_561.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___67_561.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___67_561.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___67_561.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____562;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____572
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___66_528.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___66_528.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___66_528.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___66_528.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____529;
                                 FStar_Syntax_Syntax.bind_wp = uu____530;
                                 FStar_Syntax_Syntax.if_then_else = uu____531;
                                 FStar_Syntax_Syntax.ite_wp = uu____532;
                                 FStar_Syntax_Syntax.stronger = uu____533;
                                 FStar_Syntax_Syntax.close_wp = uu____534;
                                 FStar_Syntax_Syntax.assert_p = uu____535;
                                 FStar_Syntax_Syntax.assume_p = uu____536;
                                 FStar_Syntax_Syntax.null_wp = uu____537;
                                 FStar_Syntax_Syntax.trivial = uu____538;
                                 FStar_Syntax_Syntax.repr = uu____539;
                                 FStar_Syntax_Syntax.return_repr = uu____551;
                                 FStar_Syntax_Syntax.bind_repr = uu____552;
                                 FStar_Syntax_Syntax.actions = uu____553;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___66_528.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____612 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____617 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____612 uu____617  in
                           let uu____624 =
                             let uu____625 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____625.FStar_Syntax_Syntax.n  in
                           match uu____624 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____660)::(wp,uu____662)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____677 -> fail1 signature1)
                           | uu____678 -> fail1 signature1  in
                         let uu____679 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____679 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____702 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____709 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____709 with
                                     | (signature1,uu____721) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____722 ->
                                    let uu____725 =
                                      let uu____730 =
                                        let uu____731 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____731)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____730
                                       in
                                    (match uu____725 with
                                     | (uu____740,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____743 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____743
                                 in
                              let uu____744 =
                                let uu____745 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____745
                                then
                                  let uu____746 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____747 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____748 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____749 =
                                    let uu____750 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____750
                                     in
                                  let uu____751 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____746 uu____747 uu____748 uu____749
                                    uu____751
                                else ()  in
                              let check_and_gen' env3 uu____770 k =
                                match uu____770 with
                                | (us,t) ->
                                    (match annotated_univ_names with
                                     | [] -> check_and_gen env3 t k
                                     | uu____784::uu____785 ->
                                         let uu____788 =
                                           FStar_Syntax_Subst.subst_tscheme
                                             open_annotated_univs (us, t)
                                            in
                                         (match uu____788 with
                                          | (us1,t1) ->
                                              let uu____797 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  us1 t1
                                                 in
                                              (match uu____797 with
                                               | (us2,t2) ->
                                                   let uu____804 =
                                                     let uu____805 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env3 us2
                                                        in
                                                     tc_check_trivial_guard
                                                       uu____805 t2 k
                                                      in
                                                   let uu____806 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       us2 t2
                                                      in
                                                   (us2, uu____806))))
                                 in
                              let return_wp =
                                let expected_k =
                                  let uu____811 =
                                    let uu____818 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____819 =
                                      let uu____822 =
                                        let uu____823 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____823
                                         in
                                      [uu____822]  in
                                    uu____818 :: uu____819  in
                                  let uu____824 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                  FStar_Syntax_Util.arrow uu____811 uu____824
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                 in
                              let bind_wp =
                                let uu____828 = fresh_effect_signature ()  in
                                match uu____828 with
                                | (b,wp_b) ->
                                    let a_wp_b =
                                      let uu____844 =
                                        let uu____851 =
                                          let uu____852 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____852
                                           in
                                        [uu____851]  in
                                      let uu____853 =
                                        FStar_Syntax_Syntax.mk_Total wp_b  in
                                      FStar_Syntax_Util.arrow uu____844
                                        uu____853
                                       in
                                    let expected_k =
                                      let uu____859 =
                                        let uu____866 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____867 =
                                          let uu____870 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____871 =
                                            let uu____874 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____875 =
                                              let uu____878 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____879 =
                                                let uu____882 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    a_wp_b
                                                   in
                                                [uu____882]  in
                                              uu____878 :: uu____879  in
                                            uu____874 :: uu____875  in
                                          uu____870 :: uu____871  in
                                        uu____866 :: uu____867  in
                                      let uu____883 =
                                        FStar_Syntax_Syntax.mk_Total wp_b  in
                                      FStar_Syntax_Util.arrow uu____859
                                        uu____883
                                       in
                                    check_and_gen' env2
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      expected_k
                                 in
                              let if_then_else1 =
                                let p =
                                  let uu____888 =
                                    let uu____891 =
                                      FStar_Ident.range_of_lid
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    FStar_Pervasives_Native.Some uu____891
                                     in
                                  let uu____892 =
                                    let uu____893 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_right uu____893
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_Syntax_Syntax.new_bv uu____888
                                    uu____892
                                   in
                                let expected_k =
                                  let uu____905 =
                                    let uu____912 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____913 =
                                      let uu____916 =
                                        FStar_Syntax_Syntax.mk_binder p  in
                                      let uu____917 =
                                        let uu____920 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        let uu____921 =
                                          let uu____924 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____924]  in
                                        uu____920 :: uu____921  in
                                      uu____916 :: uu____917  in
                                    uu____912 :: uu____913  in
                                  let uu____925 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____905 uu____925
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.if_then_else
                                  expected_k
                                 in
                              let ite_wp =
                                let expected_k =
                                  let uu____932 =
                                    let uu____939 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____940 =
                                      let uu____943 =
                                        FStar_Syntax_Syntax.null_binder wp_a
                                         in
                                      [uu____943]  in
                                    uu____939 :: uu____940  in
                                  let uu____944 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____932 uu____944
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                 in
                              let stronger =
                                let uu____948 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____948 with
                                | (t,uu____954) ->
                                    let expected_k =
                                      let uu____958 =
                                        let uu____965 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____966 =
                                          let uu____969 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____970 =
                                            let uu____973 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____973]  in
                                          uu____969 :: uu____970  in
                                        uu____965 :: uu____966  in
                                      let uu____974 =
                                        FStar_Syntax_Syntax.mk_Total t  in
                                      FStar_Syntax_Util.arrow uu____958
                                        uu____974
                                       in
                                    check_and_gen' env2
                                      ed2.FStar_Syntax_Syntax.stronger
                                      expected_k
                                 in
                              let close_wp =
                                let b =
                                  let uu____979 =
                                    let uu____982 =
                                      FStar_Ident.range_of_lid
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    FStar_Pervasives_Native.Some uu____982
                                     in
                                  let uu____983 =
                                    let uu____984 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_right uu____984
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_Syntax_Syntax.new_bv uu____979
                                    uu____983
                                   in
                                let b_wp_a =
                                  let uu____996 =
                                    let uu____1003 =
                                      let uu____1004 =
                                        FStar_Syntax_Syntax.bv_to_name b  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____1004
                                       in
                                    [uu____1003]  in
                                  let uu____1005 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____996
                                    uu____1005
                                   in
                                let expected_k =
                                  let uu____1011 =
                                    let uu____1018 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____1019 =
                                      let uu____1022 =
                                        FStar_Syntax_Syntax.mk_binder b  in
                                      let uu____1023 =
                                        let uu____1026 =
                                          FStar_Syntax_Syntax.null_binder
                                            b_wp_a
                                           in
                                        [uu____1026]  in
                                      uu____1022 :: uu____1023  in
                                    uu____1018 :: uu____1019  in
                                  let uu____1027 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____1011
                                    uu____1027
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.close_wp expected_k
                                 in
                              let assert_p =
                                let expected_k =
                                  let uu____1034 =
                                    let uu____1041 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____1042 =
                                      let uu____1045 =
                                        let uu____1046 =
                                          let uu____1047 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____1047
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1046
                                         in
                                      let uu____1056 =
                                        let uu____1059 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1059]  in
                                      uu____1045 :: uu____1056  in
                                    uu____1041 :: uu____1042  in
                                  let uu____1060 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____1034
                                    uu____1060
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.assert_p expected_k
                                 in
                              let assume_p =
                                let expected_k =
                                  let uu____1067 =
                                    let uu____1074 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____1075 =
                                      let uu____1078 =
                                        let uu____1079 =
                                          let uu____1080 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____1080
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1079
                                         in
                                      let uu____1089 =
                                        let uu____1092 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1092]  in
                                      uu____1078 :: uu____1089  in
                                    uu____1074 :: uu____1075  in
                                  let uu____1093 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____1067
                                    uu____1093
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.assume_p expected_k
                                 in
                              let null_wp =
                                let expected_k =
                                  let uu____1100 =
                                    let uu____1107 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    [uu____1107]  in
                                  let uu____1108 =
                                    FStar_Syntax_Syntax.mk_Total wp_a  in
                                  FStar_Syntax_Util.arrow uu____1100
                                    uu____1108
                                   in
                                check_and_gen' env2
                                  ed2.FStar_Syntax_Syntax.null_wp expected_k
                                 in
                              let trivial_wp =
                                let uu____1112 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____1112 with
                                | (t,uu____1118) ->
                                    let expected_k =
                                      let uu____1122 =
                                        let uu____1129 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____1130 =
                                          let uu____1133 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1133]  in
                                        uu____1129 :: uu____1130  in
                                      let uu____1134 =
                                        FStar_Syntax_Syntax.mk_GTotal t  in
                                      FStar_Syntax_Util.arrow uu____1122
                                        uu____1134
                                       in
                                    check_and_gen' env2
                                      ed2.FStar_Syntax_Syntax.trivial
                                      expected_k
                                 in
                              let uu____1137 =
                                let uu____1148 =
                                  let uu____1149 =
                                    FStar_Syntax_Subst.compress
                                      ed2.FStar_Syntax_Syntax.repr
                                     in
                                  uu____1149.FStar_Syntax_Syntax.n  in
                                match uu____1148 with
                                | FStar_Syntax_Syntax.Tm_unknown  ->
                                    ((ed2.FStar_Syntax_Syntax.repr),
                                      (ed2.FStar_Syntax_Syntax.bind_repr),
                                      (ed2.FStar_Syntax_Syntax.return_repr),
                                      (ed2.FStar_Syntax_Syntax.actions))
                                | uu____1164 ->
                                    let repr =
                                      let uu____1166 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____1166 with
                                      | (t,uu____1172) ->
                                          let expected_k =
                                            let uu____1176 =
                                              let uu____1183 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____1184 =
                                                let uu____1187 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____1187]  in
                                              uu____1183 :: uu____1184  in
                                            let uu____1188 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____1176 uu____1188
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
                                      let uu____1203 =
                                        let uu____1208 =
                                          let uu____1209 =
                                            let uu____1224 =
                                              let uu____1227 =
                                                FStar_Syntax_Syntax.as_arg t
                                                 in
                                              let uu____1228 =
                                                let uu____1231 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    wp
                                                   in
                                                [uu____1231]  in
                                              uu____1227 :: uu____1228  in
                                            (repr1, uu____1224)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____1209
                                           in
                                        FStar_Syntax_Syntax.mk uu____1208  in
                                      uu____1203 FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    let mk_repr a1 wp =
                                      let uu____1248 =
                                        FStar_Syntax_Syntax.bv_to_name a1  in
                                      mk_repr' uu____1248 wp  in
                                    let destruct_repr t =
                                      let uu____1262 =
                                        let uu____1263 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____1263.FStar_Syntax_Syntax.n  in
                                      match uu____1262 with
                                      | FStar_Syntax_Syntax.Tm_app
                                          (uu____1274,(t1,uu____1276)::
                                           (wp,uu____1278)::[])
                                          -> (t1, wp)
                                      | uu____1321 ->
                                          failwith "Unexpected repr type"
                                       in
                                    let bind_repr =
                                      let r =
                                        let uu____1332 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.Delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____1332
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____1333 =
                                        fresh_effect_signature ()  in
                                      match uu____1333 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____1349 =
                                              let uu____1356 =
                                                let uu____1357 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____1357
                                                 in
                                              [uu____1356]  in
                                            let uu____1358 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____1349 uu____1358
                                             in
                                          let wp_f =
                                            FStar_Syntax_Syntax.gen_bv "wp_f"
                                              FStar_Pervasives_Native.None
                                              wp_a
                                             in
                                          let wp_g =
                                            FStar_Syntax_Syntax.gen_bv "wp_g"
                                              FStar_Pervasives_Native.None
                                              a_wp_b
                                             in
                                          let x_a =
                                            let uu____1364 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____1364
                                             in
                                          let wp_g_x =
                                            let uu____1368 =
                                              let uu____1371 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  wp_g
                                                 in
                                              let uu____1372 =
                                                let uu____1373 =
                                                  let uu____1374 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      x_a
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____1374
                                                   in
                                                [uu____1373]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1371 uu____1372
                                               in
                                            uu____1368
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let res =
                                            let wp =
                                              let uu____1383 =
                                                let uu____1386 =
                                                  let uu____1387 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      bind_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1387
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____1396 =
                                                  let uu____1397 =
                                                    let uu____1400 =
                                                      let uu____1403 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____1404 =
                                                        let uu____1407 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            b
                                                           in
                                                        let uu____1408 =
                                                          let uu____1411 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          let uu____1412 =
                                                            let uu____1415 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_g
                                                               in
                                                            [uu____1415]  in
                                                          uu____1411 ::
                                                            uu____1412
                                                           in
                                                        uu____1407 ::
                                                          uu____1408
                                                         in
                                                      uu____1403 ::
                                                        uu____1404
                                                       in
                                                    r :: uu____1400  in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____1397
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1386 uu____1396
                                                 in
                                              uu____1383
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr b wp  in
                                          let maybe_range_arg =
                                            let uu____1421 =
                                              FStar_Util.for_some
                                                (FStar_Syntax_Util.attr_eq
                                                   FStar_Syntax_Util.dm4f_bind_range_attr)
                                                ed2.FStar_Syntax_Syntax.eff_attrs
                                               in
                                            if uu____1421
                                            then
                                              let uu____1424 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____1425 =
                                                let uu____1428 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                [uu____1428]  in
                                              uu____1424 :: uu____1425
                                            else []  in
                                          let expected_k =
                                            let uu____1433 =
                                              let uu____1440 =
                                                let uu____1443 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1444 =
                                                  let uu____1447 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  [uu____1447]  in
                                                uu____1443 :: uu____1444  in
                                              let uu____1448 =
                                                let uu____1451 =
                                                  let uu____1454 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      wp_f
                                                     in
                                                  let uu____1455 =
                                                    let uu____1458 =
                                                      let uu____1459 =
                                                        let uu____1460 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_f
                                                           in
                                                        mk_repr a uu____1460
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____1459
                                                       in
                                                    let uu____1461 =
                                                      let uu____1464 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_g
                                                         in
                                                      let uu____1465 =
                                                        let uu____1468 =
                                                          let uu____1469 =
                                                            let uu____1470 =
                                                              let uu____1477
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x_a
                                                                 in
                                                              [uu____1477]
                                                               in
                                                            let uu____1478 =
                                                              let uu____1481
                                                                =
                                                                mk_repr b
                                                                  wp_g_x
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_Syntax_Syntax.mk_Total
                                                                uu____1481
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              uu____1470
                                                              uu____1478
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____1469
                                                           in
                                                        [uu____1468]  in
                                                      uu____1464 ::
                                                        uu____1465
                                                       in
                                                    uu____1458 :: uu____1461
                                                     in
                                                  uu____1454 :: uu____1455
                                                   in
                                                FStar_List.append
                                                  maybe_range_arg uu____1451
                                                 in
                                              FStar_List.append uu____1440
                                                uu____1448
                                               in
                                            let uu____1482 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____1433 uu____1482
                                             in
                                          let uu____1485 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          (match uu____1485 with
                                           | (expected_k1,uu____1493,uu____1494)
                                               ->
                                               let env3 =
                                                 FStar_TypeChecker_Env.set_range
                                                   env2
                                                   (FStar_Pervasives_Native.snd
                                                      ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                  in
                                               let env4 =
                                                 let uu___68_1499 = env3  in
                                                 {
                                                   FStar_TypeChecker_Env.solver
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.solver);
                                                   FStar_TypeChecker_Env.range
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.range);
                                                   FStar_TypeChecker_Env.curmodule
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.curmodule);
                                                   FStar_TypeChecker_Env.gamma
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.gamma);
                                                   FStar_TypeChecker_Env.gamma_cache
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.gamma_cache);
                                                   FStar_TypeChecker_Env.modules
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.modules);
                                                   FStar_TypeChecker_Env.expected_typ
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.expected_typ);
                                                   FStar_TypeChecker_Env.sigtab
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.sigtab);
                                                   FStar_TypeChecker_Env.is_pattern
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.is_pattern);
                                                   FStar_TypeChecker_Env.instantiate_imp
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.instantiate_imp);
                                                   FStar_TypeChecker_Env.effects
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.effects);
                                                   FStar_TypeChecker_Env.generalize
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.generalize);
                                                   FStar_TypeChecker_Env.letrecs
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.letrecs);
                                                   FStar_TypeChecker_Env.top_level
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.top_level);
                                                   FStar_TypeChecker_Env.check_uvars
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.check_uvars);
                                                   FStar_TypeChecker_Env.use_eq
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.use_eq);
                                                   FStar_TypeChecker_Env.is_iface
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.is_iface);
                                                   FStar_TypeChecker_Env.admit
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.admit);
                                                   FStar_TypeChecker_Env.lax
                                                     = true;
                                                   FStar_TypeChecker_Env.lax_universes
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.lax_universes);
                                                   FStar_TypeChecker_Env.failhard
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.failhard);
                                                   FStar_TypeChecker_Env.nosynth
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.nosynth);
                                                   FStar_TypeChecker_Env.tc_term
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.tc_term);
                                                   FStar_TypeChecker_Env.type_of
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.type_of);
                                                   FStar_TypeChecker_Env.universe_of
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.universe_of);
                                                   FStar_TypeChecker_Env.check_type_of
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.check_type_of);
                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.use_bv_sorts);
                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.normalized_eff_names);
                                                   FStar_TypeChecker_Env.proof_ns
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.proof_ns);
                                                   FStar_TypeChecker_Env.synth_hook
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.synth_hook);
                                                   FStar_TypeChecker_Env.splice
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.splice);
                                                   FStar_TypeChecker_Env.is_native_tactic
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.is_native_tactic);
                                                   FStar_TypeChecker_Env.identifier_info
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.identifier_info);
                                                   FStar_TypeChecker_Env.tc_hooks
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.tc_hooks);
                                                   FStar_TypeChecker_Env.dsenv
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.dsenv);
                                                   FStar_TypeChecker_Env.dep_graph
                                                     =
                                                     (uu___68_1499.FStar_TypeChecker_Env.dep_graph)
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
                                        let uu____1509 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.gen_bv "x_a"
                                          FStar_Pervasives_Native.None
                                          uu____1509
                                         in
                                      let res =
                                        let wp =
                                          let uu____1516 =
                                            let uu____1519 =
                                              let uu____1520 =
                                                FStar_TypeChecker_Env.inst_tscheme
                                                  return_wp
                                                 in
                                              FStar_All.pipe_right uu____1520
                                                FStar_Pervasives_Native.snd
                                               in
                                            let uu____1529 =
                                              let uu____1530 =
                                                let uu____1533 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                let uu____1534 =
                                                  let uu____1537 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      x_a
                                                     in
                                                  [uu____1537]  in
                                                uu____1533 :: uu____1534  in
                                              FStar_List.map
                                                FStar_Syntax_Syntax.as_arg
                                                uu____1530
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              uu____1519 uu____1529
                                             in
                                          uu____1516
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        mk_repr a wp  in
                                      let expected_k =
                                        let uu____1543 =
                                          let uu____1550 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1551 =
                                            let uu____1554 =
                                              FStar_Syntax_Syntax.mk_binder
                                                x_a
                                               in
                                            [uu____1554]  in
                                          uu____1550 :: uu____1551  in
                                        let uu____1555 =
                                          FStar_Syntax_Syntax.mk_Total res
                                           in
                                        FStar_Syntax_Util.arrow uu____1543
                                          uu____1555
                                         in
                                      let uu____1558 =
                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                          env2 expected_k
                                         in
                                      match uu____1558 with
                                      | (expected_k1,uu____1572,uu____1573)
                                          ->
                                          let env3 =
                                            FStar_TypeChecker_Env.set_range
                                              env2
                                              (FStar_Pervasives_Native.snd
                                                 ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                             in
                                          let uu____1577 =
                                            check_and_gen' env3
                                              ed2.FStar_Syntax_Syntax.return_repr
                                              expected_k1
                                             in
                                          (match uu____1577 with
                                           | (univs1,repr1) ->
                                               (match univs1 with
                                                | [] -> ([], repr1)
                                                | uu____1598 ->
                                                    FStar_Errors.raise_error
                                                      (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                        "Unexpected universe-polymorphic return for effect")
                                                      repr1.FStar_Syntax_Syntax.pos))
                                       in
                                    let actions =
                                      let check_action act =
                                        let uu____1615 = ()  in
                                        let uu____1616 =
                                          if
                                            act.FStar_Syntax_Syntax.action_univs
                                              = []
                                          then (env2, act)
                                          else
                                            (let uu____1626 =
                                               FStar_Syntax_Subst.univ_var_opening
                                                 act.FStar_Syntax_Syntax.action_univs
                                                in
                                             match uu____1626 with
                                             | (usubst,uvs) ->
                                                 let uu____1649 =
                                                   FStar_TypeChecker_Env.push_univ_vars
                                                     env2 uvs
                                                    in
                                                 let uu____1650 =
                                                   let uu___69_1651 = act  in
                                                   let uu____1652 =
                                                     FStar_Syntax_Subst.subst_binders
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_params
                                                      in
                                                   let uu____1653 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_defn
                                                      in
                                                   let uu____1654 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___69_1651.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___69_1651.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.action_params
                                                       = uu____1652;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____1653;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____1654
                                                   }  in
                                                 (uu____1649, uu____1650))
                                           in
                                        match uu____1616 with
                                        | (env3,act1) ->
                                            let act_typ =
                                              let uu____1660 =
                                                let uu____1661 =
                                                  FStar_Syntax_Subst.compress
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                uu____1661.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____1660 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (bs,c) ->
                                                  let c1 =
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                      c
                                                     in
                                                  let uu____1685 =
                                                    FStar_Ident.lid_equals
                                                      c1.FStar_Syntax_Syntax.effect_name
                                                      ed2.FStar_Syntax_Syntax.mname
                                                     in
                                                  if uu____1685
                                                  then
                                                    let uu____1688 =
                                                      let uu____1691 =
                                                        let uu____1692 =
                                                          let uu____1693 =
                                                            FStar_List.hd
                                                              c1.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____1693
                                                           in
                                                        mk_repr'
                                                          c1.FStar_Syntax_Syntax.result_typ
                                                          uu____1692
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____1691
                                                       in
                                                    FStar_Syntax_Util.arrow
                                                      bs uu____1688
                                                  else
                                                    act1.FStar_Syntax_Syntax.action_typ
                                              | uu____1709 ->
                                                  act1.FStar_Syntax_Syntax.action_typ
                                               in
                                            let uu____1710 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env3 act_typ
                                               in
                                            (match uu____1710 with
                                             | (act_typ1,uu____1718,g_t) ->
                                                 let env' =
                                                   let uu___70_1721 =
                                                     FStar_TypeChecker_Env.set_expected_typ
                                                       env3 act_typ1
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       = false;
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.lax);
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___70_1721.FStar_TypeChecker_Env.dep_graph)
                                                   }  in
                                                 let uu____1722 =
                                                   let uu____1723 =
                                                     FStar_TypeChecker_Env.debug
                                                       env3
                                                       (FStar_Options.Other
                                                          "ED")
                                                      in
                                                   if uu____1723
                                                   then
                                                     let uu____1724 =
                                                       FStar_Ident.text_of_lid
                                                         act1.FStar_Syntax_Syntax.action_name
                                                        in
                                                     let uu____1725 =
                                                       FStar_Syntax_Print.term_to_string
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____1726 =
                                                       FStar_Syntax_Print.term_to_string
                                                         act_typ1
                                                        in
                                                     FStar_Util.print3
                                                       "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                       uu____1724 uu____1725
                                                       uu____1726
                                                   else ()  in
                                                 let uu____1728 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env'
                                                     act1.FStar_Syntax_Syntax.action_defn
                                                    in
                                                 (match uu____1728 with
                                                  | (act_defn,uu____1736,g_a)
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
                                                      let uu____1740 =
                                                        let act_typ3 =
                                                          FStar_Syntax_Subst.compress
                                                            act_typ2
                                                           in
                                                        match act_typ3.FStar_Syntax_Syntax.n
                                                        with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1768 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____1768
                                                             with
                                                             | (bs1,uu____1778)
                                                                 ->
                                                                 let res =
                                                                   mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                    in
                                                                 let k =
                                                                   let uu____1785
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                   FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1785
                                                                    in
                                                                 let uu____1788
                                                                   =
                                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                    in
                                                                 (match uu____1788
                                                                  with
                                                                  | (k1,uu____1800,g)
                                                                    ->
                                                                    (k1, g)))
                                                        | uu____1802 ->
                                                            let uu____1803 =
                                                              let uu____1808
                                                                =
                                                                let uu____1809
                                                                  =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                   in
                                                                let uu____1810
                                                                  =
                                                                  FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                   in
                                                                FStar_Util.format2
                                                                  "Actions must have function types (not: %s, a.k.a. %s)"
                                                                  uu____1809
                                                                  uu____1810
                                                                 in
                                                              (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                uu____1808)
                                                               in
                                                            FStar_Errors.raise_error
                                                              uu____1803
                                                              act_defn1.FStar_Syntax_Syntax.pos
                                                         in
                                                      (match uu____1740 with
                                                       | (expected_k,g_k) ->
                                                           let g =
                                                             FStar_TypeChecker_Rel.teq
                                                               env3 act_typ2
                                                               expected_k
                                                              in
                                                           let uu____1818 =
                                                             let uu____1819 =
                                                               let uu____1820
                                                                 =
                                                                 let uu____1821
                                                                   =
                                                                   FStar_TypeChecker_Rel.conj_guard
                                                                    g_t g
                                                                    in
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_k
                                                                   uu____1821
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_a
                                                                 uu____1820
                                                                in
                                                             FStar_TypeChecker_Rel.force_trivial_guard
                                                               env3
                                                               uu____1819
                                                              in
                                                           let act_typ3 =
                                                             let uu____1825 =
                                                               let uu____1826
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1826.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1825
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1849
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1849
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1858
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1858
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1880
                                                                    =
                                                                    let uu____1881
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____1881]
                                                                     in
                                                                    let uu____1882
                                                                    =
                                                                    let uu____1891
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1891]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1880;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1882;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1892
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1892))
                                                             | uu____1895 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1898 =
                                                             if
                                                               act1.FStar_Syntax_Syntax.action_univs
                                                                 = []
                                                             then
                                                               FStar_TypeChecker_Util.generalize_universes
                                                                 env3
                                                                 act_defn1
                                                             else
                                                               (let uu____1900
                                                                  =
                                                                  FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                   in
                                                                ((act1.FStar_Syntax_Syntax.action_univs),
                                                                  uu____1900))
                                                              in
                                                           (match uu____1898
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
                                                                let uu___71_1909
                                                                  = act1  in
                                                                {
                                                                  FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (
                                                                    uu___71_1909.FStar_Syntax_Syntax.action_name);
                                                                  FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (
                                                                    uu___71_1909.FStar_Syntax_Syntax.action_unqualified_name);
                                                                  FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                  FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (
                                                                    uu___71_1909.FStar_Syntax_Syntax.action_params);
                                                                  FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                  FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                }))))
                                         in
                                      FStar_All.pipe_right
                                        ed2.FStar_Syntax_Syntax.actions
                                        (FStar_List.map check_action)
                                       in
                                    (repr, bind_repr, return_repr, actions)
                                 in
                              (match uu____1137 with
                               | (repr,bind_repr,return_repr,actions) ->
                                   let t0 =
                                     let uu____1933 =
                                       FStar_Syntax_Syntax.mk_Total
                                         ed2.FStar_Syntax_Syntax.signature
                                        in
                                     FStar_Syntax_Util.arrow
                                       ed2.FStar_Syntax_Syntax.binders
                                       uu____1933
                                      in
                                   let uu____1936 =
                                     let uu____1943 =
                                       FStar_TypeChecker_Util.generalize_universes
                                         env0 t0
                                        in
                                     match uu____1943 with
                                     | (gen_univs,t) ->
                                         (match annotated_univ_names with
                                          | [] -> (gen_univs, t)
                                          | uu____1964 ->
                                              let uu____1967 =
                                                ((FStar_List.length gen_univs)
                                                   =
                                                   (FStar_List.length
                                                      annotated_univ_names))
                                                  &&
                                                  (FStar_List.forall2
                                                     (fun u1  ->
                                                        fun u2  ->
                                                          let uu____1973 =
                                                            FStar_Syntax_Syntax.order_univ_name
                                                              u1 u2
                                                             in
                                                          uu____1973 =
                                                            (Prims.parse_int "0"))
                                                     gen_univs
                                                     annotated_univ_names)
                                                 in
                                              if uu____1967
                                              then (gen_univs, t)
                                              else
                                                (let uu____1983 =
                                                   let uu____1988 =
                                                     let uu____1989 =
                                                       FStar_Util.string_of_int
                                                         (FStar_List.length
                                                            annotated_univ_names)
                                                        in
                                                     let uu____1990 =
                                                       FStar_Util.string_of_int
                                                         (FStar_List.length
                                                            gen_univs)
                                                        in
                                                     FStar_Util.format2
                                                       "Expected an effect definition with %s universes; but found %s"
                                                       uu____1989 uu____1990
                                                      in
                                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                     uu____1988)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1983
                                                   (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                      in
                                   (match uu____1936 with
                                    | (univs1,t) ->
                                        let signature1 =
                                          let uu____2004 =
                                            let uu____2009 =
                                              let uu____2010 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____2010.FStar_Syntax_Syntax.n
                                               in
                                            (effect_params, uu____2009)  in
                                          match uu____2004 with
                                          | ([],uu____2013) -> t
                                          | (uu____2024,FStar_Syntax_Syntax.Tm_arrow
                                             (uu____2025,c)) ->
                                              FStar_Syntax_Util.comp_result c
                                          | uu____2043 ->
                                              failwith
                                                "Impossible : t is an arrow"
                                           in
                                        let close1 n1 ts =
                                          let ts1 =
                                            let uu____2058 =
                                              FStar_Syntax_Subst.close_tscheme
                                                effect_params ts
                                               in
                                            FStar_Syntax_Subst.close_univ_vars_tscheme
                                              univs1 uu____2058
                                             in
                                          let m =
                                            FStar_List.length
                                              (FStar_Pervasives_Native.fst
                                                 ts1)
                                             in
                                          let uu____2062 =
                                            let uu____2063 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____2065 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____2065))
                                                && (m <> n1)
                                               in
                                            if uu____2063
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____2081 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2088 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2089 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2081 uu____2088
                                                  uu____2089
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ()  in
                                          ts1  in
                                        let close_action act =
                                          let uu____2098 =
                                            close1 (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_defn))
                                             in
                                          match uu____2098 with
                                          | (univs2,defn) ->
                                              let uu____2105 =
                                                close1
                                                  (~- (Prims.parse_int "1"))
                                                  ((act.FStar_Syntax_Syntax.action_univs),
                                                    (act.FStar_Syntax_Syntax.action_typ))
                                                 in
                                              (match uu____2105 with
                                               | (univs',typ) ->
                                                   let uu____2112 = ()  in
                                                   let uu___72_2113 = act  in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___72_2113.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___72_2113.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       = univs2;
                                                     FStar_Syntax_Syntax.action_params
                                                       =
                                                       (uu___72_2113.FStar_Syntax_Syntax.action_params);
                                                     FStar_Syntax_Syntax.action_defn
                                                       = defn;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = typ
                                                   })
                                           in
                                        let uu____2114 = ()  in
                                        let ed3 =
                                          let uu___73_2116 = ed2  in
                                          let uu____2117 =
                                            close1 (Prims.parse_int "0")
                                              return_wp
                                             in
                                          let uu____2118 =
                                            close1 (Prims.parse_int "1")
                                              bind_wp
                                             in
                                          let uu____2119 =
                                            close1 (Prims.parse_int "0")
                                              if_then_else1
                                             in
                                          let uu____2120 =
                                            close1 (Prims.parse_int "0")
                                              ite_wp
                                             in
                                          let uu____2121 =
                                            close1 (Prims.parse_int "0")
                                              stronger
                                             in
                                          let uu____2122 =
                                            close1 (Prims.parse_int "1")
                                              close_wp
                                             in
                                          let uu____2123 =
                                            close1 (Prims.parse_int "0")
                                              assert_p
                                             in
                                          let uu____2124 =
                                            close1 (Prims.parse_int "0")
                                              assume_p
                                             in
                                          let uu____2125 =
                                            close1 (Prims.parse_int "0")
                                              null_wp
                                             in
                                          let uu____2126 =
                                            close1 (Prims.parse_int "0")
                                              trivial_wp
                                             in
                                          let uu____2127 =
                                            let uu____2128 =
                                              close1 (Prims.parse_int "0")
                                                ([], repr)
                                               in
                                            FStar_Pervasives_Native.snd
                                              uu____2128
                                             in
                                          let uu____2139 =
                                            close1 (Prims.parse_int "0")
                                              return_repr
                                             in
                                          let uu____2140 =
                                            close1 (Prims.parse_int "1")
                                              bind_repr
                                             in
                                          let uu____2141 =
                                            FStar_List.map close_action
                                              actions
                                             in
                                          {
                                            FStar_Syntax_Syntax.cattributes =
                                              (uu___73_2116.FStar_Syntax_Syntax.cattributes);
                                            FStar_Syntax_Syntax.mname =
                                              (uu___73_2116.FStar_Syntax_Syntax.mname);
                                            FStar_Syntax_Syntax.univs =
                                              univs1;
                                            FStar_Syntax_Syntax.binders =
                                              effect_params;
                                            FStar_Syntax_Syntax.signature =
                                              signature1;
                                            FStar_Syntax_Syntax.ret_wp =
                                              uu____2117;
                                            FStar_Syntax_Syntax.bind_wp =
                                              uu____2118;
                                            FStar_Syntax_Syntax.if_then_else
                                              = uu____2119;
                                            FStar_Syntax_Syntax.ite_wp =
                                              uu____2120;
                                            FStar_Syntax_Syntax.stronger =
                                              uu____2121;
                                            FStar_Syntax_Syntax.close_wp =
                                              uu____2122;
                                            FStar_Syntax_Syntax.assert_p =
                                              uu____2123;
                                            FStar_Syntax_Syntax.assume_p =
                                              uu____2124;
                                            FStar_Syntax_Syntax.null_wp =
                                              uu____2125;
                                            FStar_Syntax_Syntax.trivial =
                                              uu____2126;
                                            FStar_Syntax_Syntax.repr =
                                              uu____2127;
                                            FStar_Syntax_Syntax.return_repr =
                                              uu____2139;
                                            FStar_Syntax_Syntax.bind_repr =
                                              uu____2140;
                                            FStar_Syntax_Syntax.actions =
                                              uu____2141;
                                            FStar_Syntax_Syntax.eff_attrs =
                                              (uu___73_2116.FStar_Syntax_Syntax.eff_attrs)
                                          }  in
                                        let uu____2144 =
                                          let uu____2145 =
                                            (FStar_TypeChecker_Env.debug env2
                                               FStar_Options.Low)
                                              ||
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env2)
                                                 (FStar_Options.Other "ED"))
                                             in
                                          if uu____2145
                                          then
                                            let uu____2146 =
                                              FStar_Syntax_Print.eff_decl_to_string
                                                false ed3
                                               in
                                            FStar_Util.print_string
                                              uu____2146
                                          else ()  in
                                        ed3))))))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ed  ->
      let uu____2168 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2168 with
      | (effect_binders_un,signature_un) ->
          let uu____2185 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2185 with
           | (effect_binders,env1,uu____2204) ->
               let uu____2205 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2205 with
                | (signature,uu____2221) ->
                    let raise_error1 a uu____2234 =
                      match uu____2234 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2260  ->
                           match uu____2260 with
                           | (bv,qual) ->
                               let uu____2271 =
                                 let uu___74_2272 = bv  in
                                 let uu____2273 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___74_2272.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___74_2272.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2273
                                 }  in
                               (uu____2271, qual)) effect_binders
                       in
                    let uu____2276 =
                      let uu____2283 =
                        let uu____2284 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2284.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2283 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2294)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2316 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2276 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2334 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2334
                           then
                             let uu____2335 =
                               let uu____2338 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2338  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2335
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2375 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2375 with
                           | (t2,comp,uu____2388) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2396 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2396 with
                          | (repr,_comp) ->
                              let uu____2417 =
                                let uu____2418 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2418
                                then
                                  let uu____2419 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2419
                                else ()  in
                              let dmff_env =
                                FStar_TypeChecker_DMFF.empty env1
                                  (FStar_TypeChecker_TcTerm.tc_constant env1
                                     FStar_Range.dummyRange)
                                 in
                              let wp_type =
                                FStar_TypeChecker_DMFF.star_type dmff_env
                                  repr
                                 in
                              let wp_type1 = recheck_debug "*" env1 wp_type
                                 in
                              let wp_a =
                                let uu____2425 =
                                  let uu____2426 =
                                    let uu____2427 =
                                      let uu____2442 =
                                        let uu____2449 =
                                          let uu____2454 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          let uu____2455 =
                                            FStar_Syntax_Syntax.as_implicit
                                              false
                                             in
                                          (uu____2454, uu____2455)  in
                                        [uu____2449]  in
                                      (wp_type1, uu____2442)  in
                                    FStar_Syntax_Syntax.Tm_app uu____2427  in
                                  mk1 uu____2426  in
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.Beta] env1
                                  uu____2425
                                 in
                              let effect_signature =
                                let binders =
                                  let uu____2480 =
                                    let uu____2485 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (a1, uu____2485)  in
                                  let uu____2486 =
                                    let uu____2493 =
                                      let uu____2494 =
                                        FStar_Syntax_Syntax.gen_bv
                                          "dijkstra_wp"
                                          FStar_Pervasives_Native.None wp_a
                                         in
                                      FStar_All.pipe_right uu____2494
                                        FStar_Syntax_Syntax.mk_binder
                                       in
                                    [uu____2493]  in
                                  uu____2480 :: uu____2486  in
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
                              let elaborate_and_star dmff_env1 other_binders
                                item =
                                let env2 =
                                  FStar_TypeChecker_DMFF.get_env dmff_env1
                                   in
                                let uu____2561 = item  in
                                match uu____2561 with
                                | (u_item,item1) ->
                                    let uu____2582 =
                                      open_and_check env2 other_binders item1
                                       in
                                    (match uu____2582 with
                                     | (item2,item_comp) ->
                                         let uu____2597 =
                                           let uu____2598 =
                                             let uu____2599 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 item_comp
                                                in
                                             Prims.op_Negation uu____2599  in
                                           if uu____2598
                                           then
                                             let uu____2600 =
                                               let uu____2605 =
                                                 let uu____2606 =
                                                   FStar_Syntax_Print.term_to_string
                                                     item2
                                                    in
                                                 let uu____2607 =
                                                   FStar_Syntax_Print.lcomp_to_string
                                                     item_comp
                                                    in
                                                 FStar_Util.format2
                                                   "Computation for [%s] is not total : %s !"
                                                   uu____2606 uu____2607
                                                  in
                                               (FStar_Errors.Fatal_ComputationNotTotal,
                                                 uu____2605)
                                                in
                                             FStar_Errors.raise_err
                                               uu____2600
                                           else ()  in
                                         let uu____2609 =
                                           FStar_TypeChecker_DMFF.star_expr
                                             dmff_env1 item2
                                            in
                                         (match uu____2609 with
                                          | (item_t,item_wp,item_elab) ->
                                              let item_wp1 =
                                                recheck_debug "*" env2
                                                  item_wp
                                                 in
                                              let item_elab1 =
                                                recheck_debug "_" env2
                                                  item_elab
                                                 in
                                              (dmff_env1, item_t, item_wp1,
                                                item_elab1)))
                                 in
                              let uu____2629 =
                                elaborate_and_star dmff_env []
                                  ed.FStar_Syntax_Syntax.bind_repr
                                 in
                              (match uu____2629 with
                               | (dmff_env1,uu____2653,bind_wp,bind_elab) ->
                                   let uu____2656 =
                                     elaborate_and_star dmff_env1 []
                                       ed.FStar_Syntax_Syntax.return_repr
                                      in
                                   (match uu____2656 with
                                    | (dmff_env2,uu____2680,return_wp,return_elab)
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
                                          let uu____2687 =
                                            let uu____2688 =
                                              FStar_Syntax_Subst.compress
                                                return_wp
                                               in
                                            uu____2688.FStar_Syntax_Syntax.n
                                             in
                                          Obj.magic
                                            (match uu____2687 with
                                             | FStar_Syntax_Syntax.Tm_abs
                                                 (b1::b2::bs,body,what) ->
                                                 Obj.repr
                                                   (let uu____2732 =
                                                      let uu____2747 =
                                                        let uu____2752 =
                                                          FStar_Syntax_Util.abs
                                                            bs body
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        FStar_Syntax_Subst.open_term
                                                          [b1; b2] uu____2752
                                                         in
                                                      match uu____2747 with
                                                      | (b11::b21::[],body1)
                                                          ->
                                                          (b11, b21, body1)
                                                      | uu____2816 ->
                                                          failwith
                                                            "Impossible : open_term not preserving binders arity"
                                                       in
                                                    match uu____2732 with
                                                    | (b11,b21,body1) ->
                                                        let env0 =
                                                          let uu____2855 =
                                                            FStar_TypeChecker_DMFF.get_env
                                                              dmff_env2
                                                             in
                                                          FStar_TypeChecker_Env.push_binders
                                                            uu____2855
                                                            [b11; b21]
                                                           in
                                                        let wp_b1 =
                                                          let raw_wp_b1 =
                                                            let uu____2872 =
                                                              let uu____2873
                                                                =
                                                                let uu____2888
                                                                  =
                                                                  let uu____2895
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2901
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2900,
                                                                    uu____2901)
                                                                     in
                                                                  [uu____2895]
                                                                   in
                                                                (wp_type1,
                                                                  uu____2888)
                                                                 in
                                                              FStar_Syntax_Syntax.Tm_app
                                                                uu____2873
                                                               in
                                                            mk1 uu____2872
                                                             in
                                                          FStar_TypeChecker_Normalize.normalize
                                                            [FStar_TypeChecker_Normalize.Beta]
                                                            env0 raw_wp_b1
                                                           in
                                                        let uu____2916 =
                                                          let uu____2925 =
                                                            let uu____2926 =
                                                              FStar_Syntax_Util.unascribe
                                                                wp_b1
                                                               in
                                                            FStar_TypeChecker_Normalize.eta_expand_with_type
                                                              env0 body1
                                                              uu____2926
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Util.abs_formals
                                                            uu____2925
                                                           in
                                                        (match uu____2916
                                                         with
                                                         | (bs1,body2,what')
                                                             ->
                                                             let fail1 a246 =
                                                               (Obj.magic
                                                                  (fun
                                                                    uu____2946
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2948
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    let uu____2949
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
                                                                    uu____2948
                                                                    uu____2949
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                    error_msg)))
                                                                 a246
                                                                in
                                                             let uu____2951 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    ->
                                                                   fail1 ()
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   let uu____2953
                                                                    =
                                                                    let uu____2954
                                                                    =
                                                                    let uu____2955
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____2955
                                                                     in
                                                                    if
                                                                    uu____2954
                                                                    then
                                                                    fail1 ()
                                                                    else ()
                                                                     in
                                                                   let uu____2957
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
                                                                    uu____2957
                                                                    (fun a247
                                                                     ->
                                                                    (Obj.magic
                                                                    ()) a247)
                                                                in
                                                             let wp =
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
                                                               let uu____2982
                                                                 =
                                                                 let uu____2985
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp
                                                                    in
                                                                 let uu____2986
                                                                   =
                                                                   let uu____2987
                                                                    =
                                                                    let uu____2994
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2994,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                   [uu____2987]
                                                                    in
                                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                                   uu____2985
                                                                   uu____2986
                                                                  in
                                                               uu____2982
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____3019 =
                                                               let uu____3020
                                                                 =
                                                                 let uu____3027
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_binder
                                                                    wp
                                                                    in
                                                                 [uu____3027]
                                                                  in
                                                               b11 ::
                                                                 uu____3020
                                                                in
                                                             let uu____3032 =
                                                               FStar_Syntax_Util.abs
                                                                 bs1 body3
                                                                 what
                                                                in
                                                             FStar_Syntax_Util.abs
                                                               uu____3019
                                                               uu____3032
                                                               (FStar_Pervasives_Native.Some
                                                                  rc_gtot)))
                                             | uu____3033 ->
                                                 Obj.repr
                                                   (raise_error1 ()
                                                      (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                        "unexpected shape for return")))
                                           in
                                        let return_wp1 =
                                          let uu____3035 =
                                            let uu____3036 =
                                              FStar_Syntax_Subst.compress
                                                return_wp
                                               in
                                            uu____3036.FStar_Syntax_Syntax.n
                                             in
                                          Obj.magic
                                            (match uu____3035 with
                                             | FStar_Syntax_Syntax.Tm_abs
                                                 (b1::b2::bs,body,what) ->
                                                 Obj.repr
                                                   (let uu____3080 =
                                                      FStar_Syntax_Util.abs
                                                        bs body what
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      [b1; b2] uu____3080
                                                      (FStar_Pervasives_Native.Some
                                                         rc_gtot))
                                             | uu____3093 ->
                                                 Obj.repr
                                                   (raise_error1 ()
                                                      (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                        "unexpected shape for return")))
                                           in
                                        let bind_wp1 =
                                          let uu____3095 =
                                            let uu____3096 =
                                              FStar_Syntax_Subst.compress
                                                bind_wp
                                               in
                                            uu____3096.FStar_Syntax_Syntax.n
                                             in
                                          Obj.magic
                                            (match uu____3095 with
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
                                                    let uu____3123 =
                                                      let uu____3124 =
                                                        let uu____3127 =
                                                          let uu____3128 =
                                                            mk1
                                                              (FStar_Syntax_Syntax.Tm_fvar
                                                                 r)
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____3128
                                                           in
                                                        [uu____3127]  in
                                                      FStar_List.append
                                                        uu____3124 binders
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      uu____3123 body what)
                                             | uu____3129 ->
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
                                            (let uu____3148 =
                                               let uu____3149 =
                                                 let uu____3150 =
                                                   let uu____3165 =
                                                     let uu____3166 =
                                                       FStar_Syntax_Util.args_of_binders
                                                         effect_binders1
                                                        in
                                                     FStar_Pervasives_Native.snd
                                                       uu____3166
                                                      in
                                                   (t, uu____3165)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3150
                                                  in
                                               mk1 uu____3149  in
                                             FStar_Syntax_Subst.close
                                               effect_binders1 uu____3148)
                                           in
                                        let rec apply_last1 f l =
                                          match l with
                                          | [] -> failwith "empty path.."
                                          | a2::[] ->
                                              let uu____3198 = f a2  in
                                              [uu____3198]
                                          | x::xs ->
                                              let uu____3203 =
                                                apply_last1 f xs  in
                                              x :: uu____3203
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
                                          let uu____3223 =
                                            FStar_TypeChecker_Env.try_lookup_lid
                                              env1 l'
                                             in
                                          match uu____3223 with
                                          | FStar_Pervasives_Native.Some
                                              (_us,_t) ->
                                              let uu____3252 =
                                                let uu____3253 =
                                                  FStar_Options.debug_any ()
                                                   in
                                                if uu____3253
                                                then
                                                  let uu____3254 =
                                                    FStar_Ident.string_of_lid
                                                      l'
                                                     in
                                                  FStar_Util.print1
                                                    "DM4F: Applying override %s\n"
                                                    uu____3254
                                                else ()  in
                                              let uu____3256 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  l'
                                                  FStar_Syntax_Syntax.Delta_equational
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____3256
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____3265 =
                                                let uu____3270 = mk_lid name
                                                   in
                                                let uu____3271 =
                                                  FStar_Syntax_Util.abs
                                                    effect_binders1 item
                                                    FStar_Pervasives_Native.None
                                                   in
                                                FStar_TypeChecker_Util.mk_toplevel_definition
                                                  env1 uu____3270 uu____3271
                                                 in
                                              (match uu____3265 with
                                               | (sigelt,fv) ->
                                                   let uu____3274 =
                                                     let uu____3275 =
                                                       let uu____3278 =
                                                         FStar_ST.op_Bang
                                                           sigelts
                                                          in
                                                       sigelt :: uu____3278
                                                        in
                                                     FStar_ST.op_Colon_Equals
                                                       sigelts uu____3275
                                                      in
                                                   fv)
                                           in
                                        let lift_from_pure_wp1 =
                                          register "lift_from_pure"
                                            lift_from_pure_wp
                                           in
                                        let return_wp2 =
                                          register "return_wp" return_wp1  in
                                        let uu____3381 =
                                          FStar_Options.push ()  in
                                        let uu____3382 =
                                          let uu____3383 =
                                            let uu____3386 =
                                              FStar_Syntax_Syntax.mk_sigelt
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   (FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"))
                                               in
                                            let uu____3387 =
                                              FStar_ST.op_Bang sigelts  in
                                            uu____3386 :: uu____3387  in
                                          FStar_ST.op_Colon_Equals sigelts
                                            uu____3383
                                           in
                                        let return_elab1 =
                                          register "return_elab" return_elab
                                           in
                                        let uu____3489 = FStar_Options.pop ()
                                           in
                                        let bind_wp2 =
                                          register "bind_wp" bind_wp1  in
                                        let uu____3491 =
                                          FStar_Options.push ()  in
                                        let uu____3492 =
                                          let uu____3493 =
                                            let uu____3496 =
                                              FStar_Syntax_Syntax.mk_sigelt
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   (FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"))
                                               in
                                            let uu____3497 =
                                              FStar_ST.op_Bang sigelts  in
                                            uu____3496 :: uu____3497  in
                                          FStar_ST.op_Colon_Equals sigelts
                                            uu____3493
                                           in
                                        let bind_elab1 =
                                          register "bind_elab" bind_elab  in
                                        let uu____3599 = FStar_Options.pop ()
                                           in
                                        let uu____3600 =
                                          FStar_List.fold_left
                                            (fun uu____3640  ->
                                               fun action  ->
                                                 match uu____3640 with
                                                 | (dmff_env3,actions) ->
                                                     let params_un =
                                                       FStar_Syntax_Subst.open_binders
                                                         action.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____3661 =
                                                       let uu____3668 =
                                                         FStar_TypeChecker_DMFF.get_env
                                                           dmff_env3
                                                          in
                                                       FStar_TypeChecker_TcTerm.tc_tparams
                                                         uu____3668 params_un
                                                        in
                                                     (match uu____3661 with
                                                      | (action_params,env',uu____3677)
                                                          ->
                                                          let action_params1
                                                            =
                                                            FStar_List.map
                                                              (fun uu____3697
                                                                  ->
                                                                 match uu____3697
                                                                 with
                                                                 | (bv,qual)
                                                                    ->
                                                                    let uu____3708
                                                                    =
                                                                    let uu___75_3709
                                                                    = bv  in
                                                                    let uu____3710
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___75_3709.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___75_3709.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3710
                                                                    }  in
                                                                    (uu____3708,
                                                                    qual))
                                                              action_params
                                                             in
                                                          let dmff_env' =
                                                            FStar_TypeChecker_DMFF.set_env
                                                              dmff_env3 env'
                                                             in
                                                          let uu____3714 =
                                                            elaborate_and_star
                                                              dmff_env'
                                                              action_params1
                                                              ((action.FStar_Syntax_Syntax.action_univs),
                                                                (action.FStar_Syntax_Syntax.action_defn))
                                                             in
                                                          (match uu____3714
                                                           with
                                                           | (dmff_env4,action_t,action_wp,action_elab)
                                                               ->
                                                               let name =
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
                                                                 | [] ->
                                                                    action_typ_with_wp1
                                                                 | uu____3744
                                                                    ->
                                                                    let uu____3745
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3745
                                                                  in
                                                               let uu____3748
                                                                 =
                                                                 let uu____3749
                                                                   =
                                                                   FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")
                                                                    in
                                                                 if
                                                                   uu____3749
                                                                 then
                                                                   let uu____3750
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                   let uu____3751
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                   let uu____3752
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                   let uu____3753
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                   FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3750
                                                                    uu____3751
                                                                    uu____3752
                                                                    uu____3753
                                                                 else ()  in
                                                               let action_elab3
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
                                                               let uu____3757
                                                                 =
                                                                 let uu____3760
                                                                   =
                                                                   let uu___76_3761
                                                                    = action
                                                                     in
                                                                   let uu____3762
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                   let uu____3763
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                   {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___76_3761.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___76_3761.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___76_3761.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3762;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3763
                                                                   }  in
                                                                 uu____3760
                                                                   :: actions
                                                                  in
                                                               (dmff_env4,
                                                                 uu____3757))))
                                            (dmff_env2, [])
                                            ed.FStar_Syntax_Syntax.actions
                                           in
                                        (match uu____3600 with
                                         | (dmff_env3,actions) ->
                                             let actions1 =
                                               FStar_List.rev actions  in
                                             let repr1 =
                                               let wp =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "wp_a"
                                                   FStar_Pervasives_Native.None
                                                   wp_a
                                                  in
                                               let binders =
                                                 let uu____3796 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a1
                                                    in
                                                 let uu____3797 =
                                                   let uu____3800 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp
                                                      in
                                                   [uu____3800]  in
                                                 uu____3796 :: uu____3797  in
                                               let uu____3801 =
                                                 let uu____3802 =
                                                   let uu____3803 =
                                                     let uu____3804 =
                                                       let uu____3819 =
                                                         let uu____3826 =
                                                           let uu____3831 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a1
                                                              in
                                                           let uu____3832 =
                                                             FStar_Syntax_Syntax.as_implicit
                                                               false
                                                              in
                                                           (uu____3831,
                                                             uu____3832)
                                                            in
                                                         [uu____3826]  in
                                                       (repr, uu____3819)  in
                                                     FStar_Syntax_Syntax.Tm_app
                                                       uu____3804
                                                      in
                                                   mk1 uu____3803  in
                                                 let uu____3847 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     wp
                                                    in
                                                 FStar_TypeChecker_DMFF.trans_F
                                                   dmff_env3 uu____3802
                                                   uu____3847
                                                  in
                                               FStar_Syntax_Util.abs binders
                                                 uu____3801
                                                 FStar_Pervasives_Native.None
                                                in
                                             let repr2 =
                                               recheck_debug "FC" env1 repr1
                                                in
                                             let repr3 =
                                               register "repr" repr2  in
                                             let uu____3850 =
                                               let uu____3857 =
                                                 let uu____3858 =
                                                   let uu____3861 =
                                                     FStar_Syntax_Subst.compress
                                                       wp_type1
                                                      in
                                                   FStar_All.pipe_left
                                                     FStar_Syntax_Util.unascribe
                                                     uu____3861
                                                    in
                                                 uu____3858.FStar_Syntax_Syntax.n
                                                  in
                                               Obj.magic
                                                 (match uu____3857 with
                                                  | FStar_Syntax_Syntax.Tm_abs
                                                      (type_param::effect_param,arrow1,uu____3871)
                                                      ->
                                                      Obj.repr
                                                        (let uu____3900 =
                                                           let uu____3917 =
                                                             FStar_Syntax_Subst.open_term
                                                               (type_param ::
                                                               effect_param)
                                                               arrow1
                                                              in
                                                           match uu____3917
                                                           with
                                                           | (b::bs,body) ->
                                                               (b, bs, body)
                                                           | uu____3975 ->
                                                               failwith
                                                                 "Impossible : open_term nt preserving binders arity"
                                                            in
                                                         match uu____3900
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____4025 =
                                                               let uu____4026
                                                                 =
                                                                 let uu____4029
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____4029
                                                                  in
                                                               uu____4026.FStar_Syntax_Syntax.n
                                                                in
                                                             Obj.magic
                                                               (match uu____4025
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4054
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____4054
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____4067
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4092
                                                                     ->
                                                                    match uu____4092
                                                                    with
                                                                    | 
                                                                    (bv,uu____4098)
                                                                    ->
                                                                    let uu____4099
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4100
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4099
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____4067
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
                                                                    let uu____4164
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4164
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4169
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4177
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4177
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4182
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4185
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4182,
                                                                    uu____4185)))
                                                                | uu____4192
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4193
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4199
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4198)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4193)))
                                                  | uu____4200 ->
                                                      Obj.repr
                                                        (let uu____4201 =
                                                           let uu____4206 =
                                                             let uu____4207 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 wp_type1
                                                                in
                                                             FStar_Util.format1
                                                               "Impossible: pre/post abs %s"
                                                               uu____4207
                                                              in
                                                           (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                             uu____4206)
                                                            in
                                                         raise_error1 ()
                                                           uu____4201))
                                                in
                                             (match uu____3850 with
                                              | (pre,post) ->
                                                  let uu____4224 =
                                                    let uu____4225 =
                                                      register "pre" pre  in
                                                    ()  in
                                                  let uu____4226 =
                                                    let uu____4227 =
                                                      register "post" post
                                                       in
                                                    ()  in
                                                  let uu____4228 =
                                                    let uu____4229 =
                                                      register "wp" wp_type1
                                                       in
                                                    ()  in
                                                  let ed1 =
                                                    let uu___77_4231 = ed  in
                                                    let uu____4232 =
                                                      FStar_Syntax_Subst.close_binders
                                                        effect_binders1
                                                       in
                                                    let uu____4233 =
                                                      FStar_Syntax_Subst.close
                                                        effect_binders1
                                                        effect_signature1
                                                       in
                                                    let uu____4234 =
                                                      let uu____4235 =
                                                        apply_close
                                                          return_wp2
                                                         in
                                                      ([], uu____4235)  in
                                                    let uu____4242 =
                                                      let uu____4243 =
                                                        apply_close bind_wp2
                                                         in
                                                      ([], uu____4243)  in
                                                    let uu____4250 =
                                                      apply_close repr3  in
                                                    let uu____4251 =
                                                      let uu____4252 =
                                                        apply_close
                                                          return_elab1
                                                         in
                                                      ([], uu____4252)  in
                                                    let uu____4259 =
                                                      let uu____4260 =
                                                        apply_close
                                                          bind_elab1
                                                         in
                                                      ([], uu____4260)  in
                                                    {
                                                      FStar_Syntax_Syntax.cattributes
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.cattributes);
                                                      FStar_Syntax_Syntax.mname
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.mname);
                                                      FStar_Syntax_Syntax.univs
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.univs);
                                                      FStar_Syntax_Syntax.binders
                                                        = uu____4232;
                                                      FStar_Syntax_Syntax.signature
                                                        = uu____4233;
                                                      FStar_Syntax_Syntax.ret_wp
                                                        = uu____4234;
                                                      FStar_Syntax_Syntax.bind_wp
                                                        = uu____4242;
                                                      FStar_Syntax_Syntax.if_then_else
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.if_then_else);
                                                      FStar_Syntax_Syntax.ite_wp
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.ite_wp);
                                                      FStar_Syntax_Syntax.stronger
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.stronger);
                                                      FStar_Syntax_Syntax.close_wp
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.close_wp);
                                                      FStar_Syntax_Syntax.assert_p
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.assert_p);
                                                      FStar_Syntax_Syntax.assume_p
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.assume_p);
                                                      FStar_Syntax_Syntax.null_wp
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.null_wp);
                                                      FStar_Syntax_Syntax.trivial
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.trivial);
                                                      FStar_Syntax_Syntax.repr
                                                        = uu____4250;
                                                      FStar_Syntax_Syntax.return_repr
                                                        = uu____4251;
                                                      FStar_Syntax_Syntax.bind_repr
                                                        = uu____4259;
                                                      FStar_Syntax_Syntax.actions
                                                        = actions1;
                                                      FStar_Syntax_Syntax.eff_attrs
                                                        =
                                                        (uu___77_4231.FStar_Syntax_Syntax.eff_attrs)
                                                    }  in
                                                  let uu____4267 =
                                                    FStar_TypeChecker_DMFF.gen_wps_for_free
                                                      env1 effect_binders1 a1
                                                      wp_a ed1
                                                     in
                                                  (match uu____4267 with
                                                   | (sigelts',ed2) ->
                                                       let uu____4284 =
                                                         let uu____4285 =
                                                           FStar_TypeChecker_Env.debug
                                                             env1
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____4285
                                                         then
                                                           let uu____4286 =
                                                             FStar_Syntax_Print.eff_decl_to_string
                                                               true ed2
                                                              in
                                                           FStar_Util.print_string
                                                             uu____4286
                                                         else ()  in
                                                       let lift_from_pure_opt
                                                         =
                                                         if
                                                           (FStar_List.length
                                                              effect_binders1)
                                                             =
                                                             (Prims.parse_int "0")
                                                         then
                                                           let lift_from_pure
                                                             =
                                                             let uu____4298 =
                                                               let uu____4301
                                                                 =
                                                                 let uu____4310
                                                                   =
                                                                   apply_close
                                                                    lift_from_pure_wp1
                                                                    in
                                                                 ([],
                                                                   uu____4310)
                                                                  in
                                                               FStar_Pervasives_Native.Some
                                                                 uu____4301
                                                                in
                                                             {
                                                               FStar_Syntax_Syntax.source
                                                                 =
                                                                 FStar_Parser_Const.effect_PURE_lid;
                                                               FStar_Syntax_Syntax.target
                                                                 =
                                                                 (ed2.FStar_Syntax_Syntax.mname);
                                                               FStar_Syntax_Syntax.lift_wp
                                                                 = uu____4298;
                                                               FStar_Syntax_Syntax.lift
                                                                 =
                                                                 FStar_Pervasives_Native.None
                                                             }  in
                                                           let uu____4325 =
                                                             FStar_Syntax_Syntax.mk_sigelt
                                                               (FStar_Syntax_Syntax.Sig_sub_effect
                                                                  lift_from_pure)
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____4325
                                                         else
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       let uu____4327 =
                                                         let uu____4330 =
                                                           let uu____4333 =
                                                             FStar_ST.op_Bang
                                                               sigelts
                                                              in
                                                           FStar_List.rev
                                                             uu____4333
                                                            in
                                                         FStar_List.append
                                                           uu____4330
                                                           sigelts'
                                                          in
                                                       (uu____4327, ed2,
                                                         lift_from_pure_opt))))))))))
  
let tc_lex_t :
  'Auu____4399 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4399 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____4432 = ()  in
          let err_range =
            let uu____4434 = FStar_List.hd ses  in
            uu____4434.FStar_Syntax_Syntax.sigrng  in
          let uu____4435 =
            match lids with
            | lex_t1::lex_top1::lex_cons::[] when
                ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                   &&
                   (FStar_Ident.lid_equals lex_top1
                      FStar_Parser_Const.lextop_lid))
                  &&
                  (FStar_Ident.lid_equals lex_cons
                     FStar_Parser_Const.lexcons_lid)
                -> ()
            | uu____4439 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                    "Invalid (partial) redefinition of lex_t") err_range
             in
          match ses with
          | {
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (lex_t1,uu____4443,[],t,uu____4445,uu____4446);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____4448;
              FStar_Syntax_Syntax.sigattrs = uu____4449;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,uu____4451,_t_top,_lex_t_top,_0_17,uu____4454);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____4456;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____4457;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,uu____4459,_t_cons,_lex_t_cons,_0_18,uu____4462);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____4464;
                FStar_Syntax_Syntax.sigattrs = uu____4465;_}::[]
              when
              ((_0_17 = (Prims.parse_int "0")) &&
                 (_0_18 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
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
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
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
                let uu____4524 =
                  let uu____4529 =
                    let uu____4530 =
                      let uu____4537 =
                        let uu____4538 =
                          FStar_Ident.set_lid_range
                            FStar_Parser_Const.lex_t_lid r1
                           in
                        FStar_Syntax_Syntax.fvar uu____4538
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None
                         in
                      (uu____4537, [FStar_Syntax_Syntax.U_name utop])  in
                    FStar_Syntax_Syntax.Tm_uinst uu____4530  in
                  FStar_Syntax_Syntax.mk uu____4529  in
                uu____4524 FStar_Pervasives_Native.None r1  in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
              let dc_lextop =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_top1, [utop], lex_top_t1,
                         FStar_Parser_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
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
                  let uu____4556 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1))
                      FStar_Pervasives_Native.None r2
                     in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4556
                   in
                let hd1 =
                  let uu____4558 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4558
                   in
                let tl1 =
                  let uu____4560 =
                    let uu____4561 =
                      let uu____4566 =
                        let uu____4567 =
                          let uu____4574 =
                            let uu____4575 =
                              FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2
                               in
                            FStar_Syntax_Syntax.fvar uu____4575
                              FStar_Syntax_Syntax.Delta_constant
                              FStar_Pervasives_Native.None
                             in
                          (uu____4574, [FStar_Syntax_Syntax.U_name ucons2])
                           in
                        FStar_Syntax_Syntax.Tm_uinst uu____4567  in
                      FStar_Syntax_Syntax.mk uu____4566  in
                    uu____4561 FStar_Pervasives_Native.None r2  in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4560
                   in
                let res =
                  let uu____4584 =
                    let uu____4589 =
                      let uu____4590 =
                        let uu____4597 =
                          let uu____4598 =
                            FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r2
                             in
                          FStar_Syntax_Syntax.fvar uu____4598
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None
                           in
                        (uu____4597,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]])
                         in
                      FStar_Syntax_Syntax.Tm_uinst uu____4590  in
                    FStar_Syntax_Syntax.mk uu____4589  in
                  uu____4584 FStar_Pervasives_Native.None r2  in
                let uu____4604 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a,
                     (FStar_Pervasives_Native.Some
                        FStar_Syntax_Syntax.imp_tag));
                  (hd1, FStar_Pervasives_Native.None);
                  (tl1, FStar_Pervasives_Native.None)] uu____4604
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
                         FStar_Parser_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r2;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }  in
              let uu____4643 = FStar_TypeChecker_Env.get_range env  in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____4643;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }
          | uu____4648 ->
              let err_msg =
                let uu____4652 =
                  let uu____4653 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                     in
                  FStar_Syntax_Print.sigelt_to_string uu____4653  in
                FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                  uu____4652
                 in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                err_range
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.formula ->
      FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun phi  ->
      fun r  ->
        let env1 = FStar_TypeChecker_Env.set_range env r  in
        let uu____4674 = FStar_Syntax_Util.type_u ()  in
        match uu____4674 with
        | (k,uu____4680) ->
            let phi1 =
              let uu____4682 = tc_check_trivial_guard env1 phi k  in
              FStar_All.pipe_right uu____4682
                (FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env1)
               in
            let uu____4683 = FStar_TypeChecker_Util.check_uvars r phi1  in
            phi1
  
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
          let uu____4723 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4723 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4754 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____4754 FStar_List.flatten  in
              let uu____4767 =
                let uu____4768 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____4770 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____4770)
                   in
                if uu____4768
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle  in
                   let b =
                     FStar_List.iter
                       (fun ty  ->
                          let b =
                            FStar_TypeChecker_TcInductive.check_positivity ty
                              env2
                             in
                          if Prims.op_Negation b
                          then
                            let uu____4781 =
                              match ty.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                  (lid,uu____4791,uu____4792,uu____4793,uu____4794,uu____4795)
                                  -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                              | uu____4804 -> failwith "Impossible!"  in
                            match uu____4781 with
                            | (lid,r) ->
                                FStar_Errors.log_issue r
                                  (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                    (Prims.strcat "Inductive type "
                                       (Prims.strcat lid.FStar_Ident.str
                                          " does not satisfy the positivity condition")))
                          else ()) tcs
                      in
                   ())
                 in
              let skip_prims_type uu____4816 =
                let lid =
                  let ty = FStar_List.hd tcs  in
                  match ty.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,uu____4820,uu____4821,uu____4822,uu____4823,uu____4824)
                      -> lid
                  | uu____4833 -> failwith "Impossible"  in
                FStar_List.existsb
                  (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                  FStar_TypeChecker_TcInductive.early_prims_inductives
                 in
              let is_noeq =
                FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                  quals
                 in
              let res =
                let uu____4846 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env1.FStar_TypeChecker_Env.curmodule
                         FStar_Parser_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____4846
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
              let uu____4867 =
                let uu____4868 =
                  FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                ()  in
              res
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____4875 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____4875 en  in
    let uu____4876 =
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()  in
    env
  
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
      let uu____4904 = FStar_TypeChecker_Util.check_sigelt_quals env1 se  in
      let r = se.FStar_Syntax_Syntax.sigrng  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4914 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4939 ->
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
            let uu____4994 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env2)
               in
            if uu____4994
            then
              let ses1 =
                let uu____5000 =
                  let uu____5001 =
                    let uu____5002 =
                      tc_inductive
                        (let uu___78_5011 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___78_5011.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___78_5011.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___78_5011.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___78_5011.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___78_5011.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___78_5011.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___78_5011.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___78_5011.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___78_5011.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___78_5011.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___78_5011.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___78_5011.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___78_5011.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___78_5011.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___78_5011.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___78_5011.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___78_5011.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___78_5011.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___78_5011.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___78_5011.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___78_5011.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___78_5011.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___78_5011.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___78_5011.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___78_5011.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___78_5011.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___78_5011.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___78_5011.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___78_5011.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___78_5011.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___78_5011.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___78_5011.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___78_5011.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___78_5011.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___78_5011.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___78_5011.FStar_TypeChecker_Env.dep_graph)
                         }) ses se.FStar_Syntax_Syntax.sigquals lids
                       in
                    FStar_All.pipe_right uu____5002
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____5001
                    (FStar_TypeChecker_Normalize.elim_uvars env2)
                   in
                FStar_All.pipe_right uu____5000
                  FStar_Syntax_Util.ses_of_sigbundle
                 in
              let uu____5022 =
                let uu____5023 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____5023
                then
                  let uu____5024 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___79_5027 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___79_5027.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___79_5027.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___79_5027.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___79_5027.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Inductive after phase 1: %s\n"
                    uu____5024
                else ()  in
              ses1
            else ses  in
          let uu____5034 =
            tc_inductive env2 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
          (match uu____5034 with
           | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____5060 = FStar_Syntax_Util.process_pragma p r  in
          ([se], [])
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
          let uu____5066 = cps_and_elaborate env1 ne  in
          (match uu____5066 with
           | (ses,ne1,lift_from_pure_opt) ->
               let effect_and_lift_ses =
                 match lift_from_pure_opt with
                 | FStar_Pervasives_Native.Some lift ->
                     [(let uu___80_5103 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___80_5103.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___80_5103.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___80_5103.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___80_5103.FStar_Syntax_Syntax.sigattrs)
                       });
                     lift]
                 | FStar_Pervasives_Native.None  ->
                     [(let uu___81_5105 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___81_5105.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___81_5105.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___81_5105.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___81_5105.FStar_Syntax_Syntax.sigattrs)
                       })]
                  in
               ([], (FStar_List.append ses effect_and_lift_ses)))
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let ne1 =
            let uu____5112 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1)
               in
            if uu____5112
            then
              let ne1 =
                let uu____5114 =
                  let uu____5115 =
                    let uu____5116 =
                      tc_eff_decl
                        (let uu___82_5119 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___82_5119.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___82_5119.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___82_5119.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___82_5119.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___82_5119.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___82_5119.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___82_5119.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___82_5119.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___82_5119.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___82_5119.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___82_5119.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___82_5119.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___82_5119.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___82_5119.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___82_5119.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___82_5119.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___82_5119.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___82_5119.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___82_5119.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___82_5119.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___82_5119.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___82_5119.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___82_5119.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___82_5119.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___82_5119.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___82_5119.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___82_5119.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___82_5119.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___82_5119.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___82_5119.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___82_5119.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___82_5119.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___82_5119.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___82_5119.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___82_5119.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___82_5119.FStar_TypeChecker_Env.dep_graph)
                         }) ne
                       in
                    FStar_All.pipe_right uu____5116
                      (fun ne1  ->
                         let uu___83_5123 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ne1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5123.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5123.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5123.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5123.FStar_Syntax_Syntax.sigattrs)
                         })
                     in
                  FStar_All.pipe_right uu____5115
                    (FStar_TypeChecker_Normalize.elim_uvars env1)
                   in
                FStar_All.pipe_right uu____5114
                  FStar_Syntax_Util.eff_decl_of_new_effect
                 in
              let uu____5124 =
                let uu____5125 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____5125
                then
                  let uu____5126 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___84_5129 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___84_5129.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___84_5129.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___84_5129.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___84_5129.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Effect decl after phase 1: %s\n"
                    uu____5126
                else ()  in
              ne1
            else ne  in
          let ne2 = tc_eff_decl env1 ne1  in
          let se1 =
            let uu___85_5134 = se  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_new_effect ne2);
              FStar_Syntax_Syntax.sigrng =
                (uu___85_5134.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals =
                (uu___85_5134.FStar_Syntax_Syntax.sigquals);
              FStar_Syntax_Syntax.sigmeta =
                (uu___85_5134.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___85_5134.FStar_Syntax_Syntax.sigattrs)
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
          let uu____5142 =
            let uu____5149 =
              FStar_TypeChecker_Env.lookup_effect_lid env1
                sub1.FStar_Syntax_Syntax.source
               in
            monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5149
             in
          (match uu____5142 with
           | (a,wp_a_src) ->
               let uu____5164 =
                 let uu____5171 =
                   FStar_TypeChecker_Env.lookup_effect_lid env1
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env1 sub1.FStar_Syntax_Syntax.target
                   uu____5171
                  in
               (match uu____5164 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____5187 =
                        let uu____5190 =
                          let uu____5191 =
                            let uu____5198 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____5198)  in
                          FStar_Syntax_Syntax.NT uu____5191  in
                        [uu____5190]  in
                      FStar_Syntax_Subst.subst uu____5187 wp_b_tgt  in
                    let expected_k =
                      let uu____5202 =
                        let uu____5209 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____5210 =
                          let uu____5213 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____5213]  in
                        uu____5209 :: uu____5210  in
                      let uu____5214 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____5202 uu____5214  in
                    let repr_type eff_name a1 wp =
                      let no_reify l =
                        let uu____5239 =
                          let uu____5244 =
                            FStar_Util.format1 "Effect %s cannot be reified"
                              l.FStar_Ident.str
                             in
                          (FStar_Errors.Fatal_EffectCannotBeReified,
                            uu____5244)
                           in
                        let uu____5245 = FStar_TypeChecker_Env.get_range env1
                           in
                        FStar_Errors.raise_error uu____5239 uu____5245  in
                      let uu____5248 =
                        FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                         in
                      match uu____5248 with
                      | FStar_Pervasives_Native.None  -> no_reify eff_name
                      | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                          let repr =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [FStar_Syntax_Syntax.U_unknown] env1 ed
                              ([], (ed.FStar_Syntax_Syntax.repr))
                             in
                          let uu____5280 =
                            let uu____5281 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            Prims.op_Negation uu____5281  in
                          if uu____5280
                          then no_reify eff_name
                          else
                            (let uu____5287 =
                               FStar_TypeChecker_Env.get_range env1  in
                             let uu____5288 =
                               let uu____5293 =
                                 let uu____5294 =
                                   let uu____5309 =
                                     let uu____5312 =
                                       FStar_Syntax_Syntax.as_arg a1  in
                                     let uu____5313 =
                                       let uu____5316 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____5316]  in
                                     uu____5312 :: uu____5313  in
                                   (repr, uu____5309)  in
                                 FStar_Syntax_Syntax.Tm_app uu____5294  in
                               FStar_Syntax_Syntax.mk uu____5293  in
                             uu____5288 FStar_Pervasives_Native.None
                               uu____5287)
                       in
                    let uu____5322 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____5374 =
                            if
                              (FStar_List.length uvs) > (Prims.parse_int "0")
                            then
                              let uu____5383 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____5383 with
                              | (usubst,uvs1) ->
                                  let uu____5406 =
                                    FStar_TypeChecker_Env.push_univ_vars env1
                                      uvs1
                                     in
                                  let uu____5407 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____5406, uu____5407)
                            else (env1, lift_wp)  in
                          (match uu____5374 with
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
                                    let uu____5420 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____5420))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____5447 =
                            if
                              (FStar_List.length what) >
                                (Prims.parse_int "0")
                            then
                              let uu____5460 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____5460 with
                              | (usubst,uvs) ->
                                  let uu____5485 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____5485)
                            else ([], lift)  in
                          (match uu____5447 with
                           | (uvs,lift1) ->
                               let uu____5503 =
                                 let uu____5504 =
                                   FStar_TypeChecker_Env.debug env1
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____5504
                                 then
                                   let uu____5505 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____5505
                                 else ()  in
                               let dmff_env =
                                 FStar_TypeChecker_DMFF.empty env1
                                   (FStar_TypeChecker_TcTerm.tc_constant env1
                                      FStar_Range.dummyRange)
                                  in
                               let uu____5508 =
                                 let uu____5515 =
                                   FStar_TypeChecker_Env.push_univ_vars env1
                                     uvs
                                    in
                                 FStar_TypeChecker_TcTerm.tc_term uu____5515
                                   lift1
                                  in
                               (match uu____5508 with
                                | (lift2,comp,uu____5524) ->
                                    let uu____5525 =
                                      FStar_TypeChecker_DMFF.star_expr
                                        dmff_env lift2
                                       in
                                    (match uu____5525 with
                                     | (uu____5538,lift_wp,lift_elab) ->
                                         let uu____5541 =
                                           recheck_debug "lift-wp" env1
                                             lift_wp
                                            in
                                         let uu____5542 =
                                           recheck_debug "lift-elab" env1
                                             lift_elab
                                            in
                                         let uu____5543 =
                                           let uu____5552 =
                                             let uu____5559 =
                                               FStar_Syntax_Subst.close_univ_vars
                                                 uvs lift_elab
                                                in
                                             (uvs, uu____5559)  in
                                           FStar_Pervasives_Native.Some
                                             uu____5552
                                            in
                                         let uu____5568 =
                                           let uu____5575 =
                                             FStar_Syntax_Subst.close_univ_vars
                                               uvs lift_wp
                                              in
                                           (uvs, uu____5575)  in
                                         (uu____5543, uu____5568))))
                       in
                    (match uu____5322 with
                     | (lift,lift_wp) ->
                         let env2 =
                           let uu___86_5607 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___86_5607.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___86_5607.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___86_5607.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___86_5607.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___86_5607.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___86_5607.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___86_5607.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___86_5607.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___86_5607.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___86_5607.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___86_5607.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___86_5607.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___86_5607.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___86_5607.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___86_5607.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___86_5607.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___86_5607.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___86_5607.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___86_5607.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___86_5607.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___86_5607.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___86_5607.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___86_5607.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___86_5607.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___86_5607.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___86_5607.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___86_5607.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___86_5607.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___86_5607.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___86_5607.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___86_5607.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___86_5607.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___86_5607.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___86_5607.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___86_5607.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___86_5607.FStar_TypeChecker_Env.dep_graph)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____5625 =
                                 let uu____5630 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____5630 with
                                 | (usubst,uvs1) ->
                                     let uu____5653 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env2 uvs1
                                        in
                                     let uu____5654 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____5653, uu____5654)
                                  in
                               (match uu____5625 with
                                | (env3,lift2) ->
                                    let uu____5659 =
                                      let uu____5666 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env3
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env3
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____5666
                                       in
                                    (match uu____5659 with
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
                                             let uu____5690 =
                                               FStar_TypeChecker_Env.get_range
                                                 env3
                                                in
                                             let uu____5691 =
                                               let uu____5696 =
                                                 let uu____5697 =
                                                   let uu____5712 =
                                                     let uu____5715 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____5716 =
                                                       let uu____5719 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____5719]  in
                                                     uu____5715 :: uu____5716
                                                      in
                                                   (lift_wp1, uu____5712)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____5697
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____5696
                                                in
                                             uu____5691
                                               FStar_Pervasives_Native.None
                                               uu____5690
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____5728 =
                                             let uu____5735 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____5736 =
                                               let uu____5739 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____5740 =
                                                 let uu____5743 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____5743]  in
                                               uu____5739 :: uu____5740  in
                                             uu____5735 :: uu____5736  in
                                           let uu____5744 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____5728
                                             uu____5744
                                            in
                                         let uu____5747 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env3 expected_k1
                                            in
                                         (match uu____5747 with
                                          | (expected_k2,uu____5757,uu____5758)
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
                                                       env3 lift2 expected_k2
                                                      in
                                                   let uu____5762 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____5762))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         let sub2 =
                           let uu___87_5766 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___87_5766.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___87_5766.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           }  in
                         let se1 =
                           let uu___88_5768 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___88_5768.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___88_5768.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___88_5768.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___88_5768.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ([se1], []))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
          let env0 = env1  in
          let uu____5783 =
            if (FStar_List.length uvs) = (Prims.parse_int "0")
            then (env1, uvs, tps, c)
            else
              (let uu____5801 = FStar_Syntax_Subst.univ_var_opening uvs  in
               match uu____5801 with
               | (usubst,uvs1) ->
                   let tps1 = FStar_Syntax_Subst.subst_binders usubst tps  in
                   let c1 =
                     let uu____5830 =
                       FStar_Syntax_Subst.shift_subst
                         (FStar_List.length tps1) usubst
                        in
                     FStar_Syntax_Subst.subst_comp uu____5830 c  in
                   let uu____5837 =
                     FStar_TypeChecker_Env.push_univ_vars env1 uvs1  in
                   (uu____5837, uvs1, tps1, c1))
             in
          (match uu____5783 with
           | (env2,uvs1,tps1,c1) ->
               let env3 = FStar_TypeChecker_Env.set_range env2 r  in
               let uu____5853 = FStar_Syntax_Subst.open_comp tps1 c1  in
               (match uu____5853 with
                | (tps2,c2) ->
                    let uu____5868 =
                      FStar_TypeChecker_TcTerm.tc_tparams env3 tps2  in
                    (match uu____5868 with
                     | (tps3,env4,us) ->
                         let uu____5886 =
                           FStar_TypeChecker_TcTerm.tc_comp env4 c2  in
                         (match uu____5886 with
                          | (c3,u,g) ->
                              let uu____5904 =
                                FStar_TypeChecker_Rel.force_trivial_guard
                                  env4 g
                                 in
                              let tps4 =
                                FStar_Syntax_Subst.close_binders tps3  in
                              let c4 = FStar_Syntax_Subst.close_comp tps4 c3
                                 in
                              let uu____5907 =
                                let uu____5908 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_arrow (tps4, c4))
                                    FStar_Pervasives_Native.None r
                                   in
                                FStar_TypeChecker_Util.generalize_universes
                                  env0 uu____5908
                                 in
                              (match uu____5907 with
                               | (uvs2,t) ->
                                   let uu____5923 =
                                     let uu____5936 =
                                       let uu____5941 =
                                         let uu____5942 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____5942.FStar_Syntax_Syntax.n  in
                                       (tps4, uu____5941)  in
                                     match uu____5936 with
                                     | ([],FStar_Syntax_Syntax.Tm_arrow
                                        (uu____5957,c5)) -> ([], c5)
                                     | (uu____5997,FStar_Syntax_Syntax.Tm_arrow
                                        (tps5,c5)) -> (tps5, c5)
                                     | uu____6024 ->
                                         failwith
                                           "Impossible (t is an arrow)"
                                      in
                                   (match uu____5923 with
                                    | (tps5,c5) ->
                                        let uu____6067 =
                                          if
                                            (FStar_List.length uvs2) <>
                                              (Prims.parse_int "1")
                                          then
                                            let uu____6068 =
                                              FStar_Syntax_Subst.open_univ_vars
                                                uvs2 t
                                               in
                                            match uu____6068 with
                                            | (uu____6073,t1) ->
                                                let uu____6075 =
                                                  let uu____6080 =
                                                    let uu____6081 =
                                                      FStar_Syntax_Print.lid_to_string
                                                        lid
                                                       in
                                                    let uu____6082 =
                                                      FStar_All.pipe_right
                                                        (FStar_List.length
                                                           uvs2)
                                                        FStar_Util.string_of_int
                                                       in
                                                    let uu____6083 =
                                                      FStar_Syntax_Print.term_to_string
                                                        t1
                                                       in
                                                    FStar_Util.format3
                                                      "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                      uu____6081 uu____6082
                                                      uu____6083
                                                     in
                                                  (FStar_Errors.Fatal_TooManyUniverse,
                                                    uu____6080)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____6075 r
                                          else ()  in
                                        let se1 =
                                          let uu___89_6086 = se  in
                                          {
                                            FStar_Syntax_Syntax.sigel =
                                              (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                 (lid, uvs2, tps5, c5,
                                                   flags1));
                                            FStar_Syntax_Syntax.sigrng =
                                              (uu___89_6086.FStar_Syntax_Syntax.sigrng);
                                            FStar_Syntax_Syntax.sigquals =
                                              (uu___89_6086.FStar_Syntax_Syntax.sigquals);
                                            FStar_Syntax_Syntax.sigmeta =
                                              (uu___89_6086.FStar_Syntax_Syntax.sigmeta);
                                            FStar_Syntax_Syntax.sigattrs =
                                              (uu___89_6086.FStar_Syntax_Syntax.sigattrs)
                                          }  in
                                        ([se1], [])))))))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____6103,uu____6104,uu____6105) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___58_6109  ->
                  match uu___58_6109 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6110 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_let (uu____6115,uu____6116) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___58_6124  ->
                  match uu___58_6124 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6125 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let env2 = FStar_TypeChecker_Env.set_range env1 r  in
          let uu____6134 =
            let uu____6135 = FStar_TypeChecker_Env.lid_exists env2 lid  in
            if uu____6135
            then
              let uu____6136 =
                let uu____6141 =
                  let uu____6142 = FStar_Ident.text_of_lid lid  in
                  FStar_Util.format1
                    "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                    uu____6142
                   in
                (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                  uu____6141)
                 in
              FStar_Errors.raise_error uu____6136 r
            else ()  in
          let uu____6144 =
            if uvs = []
            then
              let uu____6145 =
                let uu____6146 = FStar_Syntax_Util.type_u ()  in
                FStar_Pervasives_Native.fst uu____6146  in
              check_and_gen env2 t uu____6145
            else
              (let uu____6152 = FStar_Syntax_Subst.open_univ_vars uvs t  in
               match uu____6152 with
               | (uvs1,t1) ->
                   let env3 = FStar_TypeChecker_Env.push_univ_vars env2 uvs1
                      in
                   let t2 =
                     let uu____6161 =
                       let uu____6162 = FStar_Syntax_Util.type_u ()  in
                       FStar_Pervasives_Native.fst uu____6162  in
                     tc_check_trivial_guard env3 t1 uu____6161  in
                   let t3 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.NoFullNorm;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env3
                       t2
                      in
                   let uu____6168 =
                     FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                   (uvs1, uu____6168))
             in
          (match uu____6144 with
           | (uvs1,t1) ->
               let se1 =
                 let uu___90_6184 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___90_6184.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___90_6184.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___90_6184.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___90_6184.FStar_Syntax_Syntax.sigattrs)
                 }  in
               ([se1], []))
      | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
          let uu____6194 = FStar_Syntax_Subst.open_univ_vars us phi  in
          (match uu____6194 with
           | (us1,phi1) ->
               let env2 = FStar_TypeChecker_Env.push_univ_vars env1 us1  in
               let phi2 =
                 let uu____6211 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env2)
                    in
                 if uu____6211
                 then
                   let phi2 =
                     let uu____6213 =
                       tc_assume
                         (let uu___91_6216 = env2  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___91_6216.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___91_6216.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___91_6216.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___91_6216.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___91_6216.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___91_6216.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___91_6216.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___91_6216.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___91_6216.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___91_6216.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___91_6216.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___91_6216.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___91_6216.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___91_6216.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___91_6216.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___91_6216.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___91_6216.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___91_6216.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___91_6216.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___91_6216.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___91_6216.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___91_6216.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___91_6216.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___91_6216.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___91_6216.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___91_6216.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___91_6216.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___91_6216.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___91_6216.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___91_6216.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___91_6216.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___91_6216.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___91_6216.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___91_6216.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___91_6216.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___91_6216.FStar_TypeChecker_Env.dep_graph)
                          }) phi1 r
                        in
                     FStar_All.pipe_right uu____6213
                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                          env2)
                      in
                   let uu____6217 =
                     let uu____6218 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____6218
                     then
                       let uu____6219 =
                         FStar_Syntax_Print.term_to_string phi2  in
                       FStar_Util.print1 "Assume after phase 1: %s\n"
                         uu____6219
                     else ()  in
                   phi2
                 else phi1  in
               let phi3 = tc_assume env2 phi2 r  in
               let uu____6223 =
                 if us1 = []
                 then FStar_TypeChecker_Util.generalize_universes env2 phi3
                 else
                   (let uu____6225 =
                      FStar_Syntax_Subst.close_univ_vars us1 phi3  in
                    (us1, uu____6225))
                  in
               (match uu____6223 with
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
          let uu____6249 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
          (match uu____6249 with
           | (e1,c,g1) ->
               let uu____6267 =
                 let uu____6274 =
                   let uu____6277 =
                     FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                      in
                   FStar_Pervasives_Native.Some uu____6277  in
                 let uu____6278 =
                   let uu____6283 = FStar_Syntax_Syntax.lcomp_comp c  in
                   (e1, uu____6283)  in
                 FStar_TypeChecker_TcTerm.check_expected_effect env3
                   uu____6274 uu____6278
                  in
               (match uu____6267 with
                | (e2,uu____6293,g) ->
                    let uu____6295 =
                      let uu____6296 = FStar_TypeChecker_Rel.conj_guard g1 g
                         in
                      FStar_TypeChecker_Rel.force_trivial_guard env3
                        uu____6296
                       in
                    let se1 =
                      let uu___92_6298 = se  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_main e2);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___92_6298.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___92_6298.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___92_6298.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___92_6298.FStar_Syntax_Syntax.sigattrs)
                      }  in
                    ([se1], [])))
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____6309 =
            let uu____6310 = FStar_Options.debug_any ()  in
            if uu____6310
            then
              let uu____6311 =
                FStar_Ident.string_of_lid
                  env1.FStar_TypeChecker_Env.curmodule
                 in
              let uu____6312 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.print2 "%s: Found splice of (%s)\n" uu____6311
                uu____6312
            else ()  in
          let ses = env1.FStar_TypeChecker_Env.splice env1 t  in
          let lids' = FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
             in
          let uu____6320 =
            FStar_List.iter
              (fun lid  ->
                 let uu____6325 =
                   FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                 match uu____6325 with
                 | FStar_Pervasives_Native.Some uu____6328 -> ()
                 | FStar_Pervasives_Native.None  ->
                     let uu____6329 =
                       let uu____6334 =
                         let uu____6335 = FStar_Ident.string_of_lid lid  in
                         let uu____6336 =
                           let uu____6337 =
                             FStar_List.map FStar_Ident.string_of_lid lids'
                              in
                           FStar_All.pipe_left (FStar_String.concat ", ")
                             uu____6337
                            in
                         FStar_Util.format2
                           "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                           uu____6335 uu____6336
                          in
                       (FStar_Errors.Fatal_SplicedUndef, uu____6334)  in
                     FStar_Errors.raise_error uu____6329 r) lids
             in
          ([], ses)
      | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
          let env2 = FStar_TypeChecker_Env.set_range env1 r  in
          let check_quals_eq l qopt q =
            match qopt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some q
            | FStar_Pervasives_Native.Some q' ->
                let uu____6395 =
                  ((FStar_List.length q) = (FStar_List.length q')) &&
                    (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                       q')
                   in
                if uu____6395
                then FStar_Pervasives_Native.Some q
                else
                  (let uu____6403 =
                     let uu____6408 =
                       let uu____6409 = FStar_Syntax_Print.lid_to_string l
                          in
                       let uu____6410 = FStar_Syntax_Print.quals_to_string q
                          in
                       let uu____6411 = FStar_Syntax_Print.quals_to_string q'
                          in
                       FStar_Util.format3
                         "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                         uu____6409 uu____6410 uu____6411
                        in
                     (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                       uu____6408)
                      in
                   FStar_Errors.raise_error uu____6403 r)
             in
          let rename_parameters lb =
            let rename_in_typ def typ =
              let typ1 = FStar_Syntax_Subst.compress typ  in
              let def_bs =
                let uu____6440 =
                  let uu____6441 = FStar_Syntax_Subst.compress def  in
                  uu____6441.FStar_Syntax_Syntax.n  in
                match uu____6440 with
                | FStar_Syntax_Syntax.Tm_abs (binders,uu____6451,uu____6452)
                    -> binders
                | uu____6473 -> []  in
              match typ1 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                    (val_bs,c);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars = uu____6483;_} ->
                  let has_auto_name bv =
                    FStar_Util.starts_with
                      (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      FStar_Ident.reserved_prefix
                     in
                  let rec rename_binders1 def_bs1 val_bs1 =
                    match (def_bs1, val_bs1) with
                    | ([],uu____6564) -> val_bs1
                    | (uu____6587,[]) -> val_bs1
                    | ((body_bv,uu____6611)::bt,(val_bv,aqual)::vt) ->
                        let uu____6648 = rename_binders1 bt vt  in
                        ((match ((has_auto_name body_bv),
                                  (has_auto_name val_bv))
                          with
                          | (true ,uu____6664) -> (val_bv, aqual)
                          | (false ,true ) ->
                              ((let uu___93_6666 = val_bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (let uu___94_6669 =
                                       val_bv.FStar_Syntax_Syntax.ppname  in
                                     {
                                       FStar_Ident.idText =
                                         ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                       FStar_Ident.idRange =
                                         (uu___94_6669.FStar_Ident.idRange)
                                     });
                                  FStar_Syntax_Syntax.index =
                                    (uu___93_6666.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort =
                                    (uu___93_6666.FStar_Syntax_Syntax.sort)
                                }), aqual)
                          | (false ,false ) -> (val_bv, aqual))) ::
                          uu____6648
                     in
                  let uu____6670 =
                    let uu____6675 =
                      let uu____6676 =
                        let uu____6689 = rename_binders1 def_bs val_bs  in
                        (uu____6689, c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____6676  in
                    FStar_Syntax_Syntax.mk uu____6675  in
                  uu____6670 FStar_Pervasives_Native.None r1
              | uu____6707 -> typ1  in
            let uu___95_6708 = lb  in
            let uu____6709 =
              rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                lb.FStar_Syntax_Syntax.lbtyp
               in
            {
              FStar_Syntax_Syntax.lbname =
                (uu___95_6708.FStar_Syntax_Syntax.lbname);
              FStar_Syntax_Syntax.lbunivs =
                (uu___95_6708.FStar_Syntax_Syntax.lbunivs);
              FStar_Syntax_Syntax.lbtyp = uu____6709;
              FStar_Syntax_Syntax.lbeff =
                (uu___95_6708.FStar_Syntax_Syntax.lbeff);
              FStar_Syntax_Syntax.lbdef =
                (uu___95_6708.FStar_Syntax_Syntax.lbdef);
              FStar_Syntax_Syntax.lbattrs =
                (uu___95_6708.FStar_Syntax_Syntax.lbattrs);
              FStar_Syntax_Syntax.lbpos =
                (uu___95_6708.FStar_Syntax_Syntax.lbpos)
            }  in
          let uu____6712 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.fold_left
                 (fun uu____6763  ->
                    fun lb  ->
                      match uu____6763 with
                      | (gen1,lbs1,quals_opt) ->
                          let lbname =
                            FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                             in
                          let uu____6805 =
                            let uu____6816 =
                              FStar_TypeChecker_Env.try_lookup_val_decl env2
                                (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            match uu____6816 with
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
                                  | uu____6901 ->
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
                                let uu____6940 =
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ()  in
                                let uu____6944 =
                                  FStar_Syntax_Syntax.mk_lb
                                    ((FStar_Util.Inr lbname), uvs,
                                      FStar_Parser_Const.effect_ALL_lid,
                                      tval, def,
                                      (lb.FStar_Syntax_Syntax.lbpos))
                                   in
                                (false, uu____6944, quals_opt1)
                             in
                          (match uu____6805 with
                           | (gen2,lb1,quals_opt1) ->
                               (gen2, (lb1 :: lbs1), quals_opt1)))
                 (true, [],
                   (if se.FStar_Syntax_Syntax.sigquals = []
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (se.FStar_Syntax_Syntax.sigquals))))
             in
          (match uu____6712 with
           | (should_generalize,lbs',quals_opt) ->
               let quals =
                 match quals_opt with
                 | FStar_Pervasives_Native.None  ->
                     [FStar_Syntax_Syntax.Visible_default]
                 | FStar_Pervasives_Native.Some q ->
                     let uu____7038 =
                       FStar_All.pipe_right q
                         (FStar_Util.for_some
                            (fun uu___59_7042  ->
                               match uu___59_7042 with
                               | FStar_Syntax_Syntax.Irreducible  -> true
                               | FStar_Syntax_Syntax.Visible_default  -> true
                               | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                               | uu____7043 -> false))
                        in
                     if uu____7038
                     then q
                     else FStar_Syntax_Syntax.Visible_default :: q
                  in
               let lbs'1 = FStar_List.rev lbs'  in
               let e =
                 let uu____7053 =
                   let uu____7058 =
                     let uu____7059 =
                       let uu____7072 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_constant
                              FStar_Const.Const_unit)
                           FStar_Pervasives_Native.None r
                          in
                       (((FStar_Pervasives_Native.fst lbs), lbs'1),
                         uu____7072)
                        in
                     FStar_Syntax_Syntax.Tm_let uu____7059  in
                   FStar_Syntax_Syntax.mk uu____7058  in
                 uu____7053 FStar_Pervasives_Native.None r  in
               let env0 =
                 let uu___96_7091 = env2  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___96_7091.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___96_7091.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___96_7091.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___96_7091.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___96_7091.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___96_7091.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___96_7091.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___96_7091.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___96_7091.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___96_7091.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___96_7091.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize = should_generalize;
                   FStar_TypeChecker_Env.letrecs =
                     (uu___96_7091.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = true;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___96_7091.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___96_7091.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___96_7091.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___96_7091.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___96_7091.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___96_7091.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___96_7091.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___96_7091.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___96_7091.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___96_7091.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___96_7091.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___96_7091.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___96_7091.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___96_7091.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___96_7091.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___96_7091.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___96_7091.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___96_7091.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___96_7091.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___96_7091.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___96_7091.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___96_7091.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___96_7091.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let e1 =
                 let uu____7093 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env0)
                    in
                 if uu____7093
                 then
                   let drop_lbtyp e_lax =
                     let uu____7099 =
                       let uu____7100 = FStar_Syntax_Subst.compress e_lax  in
                       uu____7100.FStar_Syntax_Syntax.n  in
                     match uu____7099 with
                     | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                         let lb_unannotated =
                           let uu____7118 =
                             let uu____7119 = FStar_Syntax_Subst.compress e
                                in
                             uu____7119.FStar_Syntax_Syntax.n  in
                           match uu____7118 with
                           | FStar_Syntax_Syntax.Tm_let
                               ((uu____7122,lb1::[]),uu____7124) ->
                               let uu____7137 =
                                 let uu____7138 =
                                   FStar_Syntax_Subst.compress
                                     lb1.FStar_Syntax_Syntax.lbtyp
                                    in
                                 uu____7138.FStar_Syntax_Syntax.n  in
                               uu____7137 = FStar_Syntax_Syntax.Tm_unknown
                           | uu____7141 ->
                               failwith
                                 "Impossible: first phase lb and second phase lb differ in structure!"
                            in
                         if lb_unannotated
                         then
                           let uu___97_7142 = e_lax  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false,
                                     [(let uu___98_7154 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           FStar_Syntax_Syntax.tun;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbdef);
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___98_7154.FStar_Syntax_Syntax.lbpos)
                                       })]), e2));
                             FStar_Syntax_Syntax.pos =
                               (uu___97_7142.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___97_7142.FStar_Syntax_Syntax.vars)
                           }
                         else e_lax
                     | uu____7156 -> e_lax  in
                   let e1 =
                     let uu____7158 =
                       let uu____7159 =
                         let uu____7160 =
                           FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                             (let uu___99_7169 = env0  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___99_7169.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___99_7169.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___99_7169.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___99_7169.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___99_7169.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___99_7169.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___99_7169.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___99_7169.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___99_7169.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___99_7169.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___99_7169.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___99_7169.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___99_7169.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___99_7169.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___99_7169.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___99_7169.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___99_7169.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___99_7169.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___99_7169.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___99_7169.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___99_7169.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___99_7169.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___99_7169.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___99_7169.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___99_7169.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___99_7169.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___99_7169.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___99_7169.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___99_7169.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___99_7169.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___99_7169.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___99_7169.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___99_7169.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___99_7169.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___99_7169.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___99_7169.FStar_TypeChecker_Env.dep_graph)
                              }) e
                            in
                         FStar_All.pipe_right uu____7160
                           (fun uu____7180  ->
                              match uu____7180 with
                              | (e1,uu____7188,uu____7189) -> e1)
                          in
                       FStar_All.pipe_right uu____7159
                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                            env0)
                        in
                     FStar_All.pipe_right uu____7158 drop_lbtyp  in
                   let uu____7190 =
                     let uu____7191 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____7191
                     then
                       let uu____7192 = FStar_Syntax_Print.term_to_string e1
                          in
                       FStar_Util.print1 "Let binding after phase 1: %s\n"
                         uu____7192
                     else ()  in
                   e1
                 else e  in
               let uu____7195 =
                 let uu____7206 =
                   FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                    in
                 match uu____7206 with
                 | ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                        (lbs1,e2);
                      FStar_Syntax_Syntax.pos = uu____7225;
                      FStar_Syntax_Syntax.vars = uu____7226;_},uu____7227,g)
                     when FStar_TypeChecker_Rel.is_trivial g ->
                     let lbs2 =
                       let uu____7256 =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs1)
                           (FStar_List.map rename_parameters)
                          in
                       ((FStar_Pervasives_Native.fst lbs1), uu____7256)  in
                     let quals1 =
                       match e2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_meta
                           (uu____7274,FStar_Syntax_Syntax.Meta_desugared
                            (FStar_Syntax_Syntax.Masked_effect ))
                           -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                       | uu____7279 -> quals  in
                     ((let uu___100_7287 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___100_7287.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___100_7287.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___100_7287.FStar_Syntax_Syntax.sigattrs)
                       }), lbs2)
                 | uu____7296 ->
                     failwith
                       "impossible (typechecking should preserve Tm_let)"
                  in
               (match uu____7195 with
                | (se1,lbs1) ->
                    let uu____7335 =
                      FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp))
                       in
                    let uu____7344 =
                      let uu____7345 = log env2  in
                      if uu____7345
                      then
                        let uu____7346 =
                          let uu____7347 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs1)
                              (FStar_List.map
                                 (fun lb  ->
                                    let should_log =
                                      let uu____7362 =
                                        let uu____7371 =
                                          let uu____7372 =
                                            let uu____7375 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            uu____7375.FStar_Syntax_Syntax.fv_name
                                             in
                                          uu____7372.FStar_Syntax_Syntax.v
                                           in
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env2 uu____7371
                                         in
                                      match uu____7362 with
                                      | FStar_Pervasives_Native.None  -> true
                                      | uu____7382 -> false  in
                                    if should_log
                                    then
                                      let uu____7391 =
                                        FStar_Syntax_Print.lbname_to_string
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      let uu____7392 =
                                        FStar_Syntax_Print.term_to_string
                                          lb.FStar_Syntax_Syntax.lbtyp
                                         in
                                      FStar_Util.format2 "let %s : %s"
                                        uu____7391 uu____7392
                                    else ""))
                             in
                          FStar_All.pipe_right uu____7347
                            (FStar_String.concat "\n")
                           in
                        FStar_Util.print1 "%s\n" uu____7346
                      else ()  in
                    ([se1], [])))
  
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
             (fun uu___60_7443  ->
                match uu___60_7443 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7444 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7451) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7457 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7466 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____7471 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7486 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7511 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7535) ->
          let uu____7544 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7544
          then
            let for_export_bundle se1 uu____7577 =
              match uu____7577 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7616,uu____7617) ->
                       let dec =
                         let uu___101_7627 = se1  in
                         let uu____7628 =
                           let uu____7629 =
                             let uu____7636 =
                               let uu____7639 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7639  in
                             (l, us, uu____7636)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7629  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7628;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___101_7627.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___101_7627.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___101_7627.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7651,uu____7652,uu____7653) ->
                       let dec =
                         let uu___102_7659 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___102_7659.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___102_7659.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___102_7659.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7664 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7686,uu____7687,uu____7688) ->
          let uu____7689 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7689 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7710 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7710
          then
            ([(let uu___103_7726 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___103_7726.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___103_7726.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___103_7726.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7728 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___61_7732  ->
                       match uu___61_7732 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7733 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7738 -> true
                       | uu____7739 -> false))
                in
             if uu____7728 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7757 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7762 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7767 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7772 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7777 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7795) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7812 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7812
          then ([], hidden)
          else
            (let dec =
               let uu____7829 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____7829;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7844 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7844
          then
            let uu____7853 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___104_7866 = se  in
                      let uu____7867 =
                        let uu____7868 =
                          let uu____7875 =
                            let uu____7876 =
                              let uu____7879 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7879.FStar_Syntax_Syntax.fv_name  in
                            uu____7876.FStar_Syntax_Syntax.v  in
                          (uu____7875, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7868  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7867;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___104_7866.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___104_7866.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___104_7866.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7853, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7903 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7920 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7935) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____7938 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7939 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7949 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7949) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7950,uu____7951,uu____7952) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7956  ->
                  match uu___62_7956 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7957 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7958,uu____7959) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___62_7967  ->
                  match uu___62_7967 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7968 -> false))
          -> env
      | uu____7969 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____8035 se =
        match uu____8035 with
        | (ses1,exports,env1,hidden) ->
            let uu____8087 =
              let uu____8088 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____8088
              then
                let uu____8089 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8089
              else ()  in
            let uu____8091 = tc_decl env1 se  in
            (match uu____8091 with
             | (ses',ses_elaborated) ->
                 let ses'1 =
                   FStar_All.pipe_right ses'
                     (FStar_List.map
                        (fun se1  ->
                           let uu____8140 =
                             let uu____8141 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____8141
                             then
                               let uu____8142 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____8142
                             else ()  in
                           FStar_TypeChecker_Normalize.elim_uvars env1 se1))
                    in
                 let ses_elaborated1 =
                   FStar_All.pipe_right ses_elaborated
                     (FStar_List.map
                        (fun se1  ->
                           FStar_TypeChecker_Normalize.elim_uvars env1 se1))
                    in
                 let uu____8153 =
                   FStar_TypeChecker_Env.promote_id_info env1
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
                          FStar_TypeChecker_Normalize.NoFullNorm] env1 t)
                    in
                 let env2 =
                   FStar_All.pipe_right ses'1
                     (FStar_List.fold_left
                        (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                        env1)
                    in
                 let uu____8163 = FStar_Syntax_Unionfind.reset ()  in
                 let uu____8164 =
                   let uu____8165 =
                     (FStar_Options.log_types ()) ||
                       (FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env2)
                          (FStar_Options.Other "LogTypes"))
                      in
                   if uu____8165
                   then
                     let uu____8166 =
                       FStar_List.fold_left
                         (fun s  ->
                            fun se1  ->
                              let uu____8172 =
                                let uu____8173 =
                                  FStar_Syntax_Print.sigelt_to_string se1  in
                                Prims.strcat uu____8173 "\n"  in
                              Prims.strcat s uu____8172) "" ses'1
                        in
                     FStar_Util.print1 "Checked: %s\n" uu____8166
                   else ()  in
                 let uu____8175 =
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses'1
                    in
                 let uu____8178 =
                   let uu____8187 = FStar_Options.use_extracted_interfaces ()
                      in
                   if uu____8187
                   then ([], [])
                   else
                     (let accum_exports_hidden uu____8224 se1 =
                        match uu____8224 with
                        | (exports1,hidden1) ->
                            let uu____8252 = for_export hidden1 se1  in
                            (match uu____8252 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'1)
                    in
                 (match uu____8178 with
                  | (exports1,hidden1) ->
                      let ses'2 =
                        FStar_List.map
                          (fun s  ->
                             let uu___105_8331 = s  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___105_8331.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___105_8331.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___105_8331.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___105_8331.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (se.FStar_Syntax_Syntax.sigattrs)
                             }) ses'1
                         in
                      (((FStar_List.rev_append ses'2 ses1), exports1, env2,
                         hidden1), ses_elaborated1)))
         in
      let process_one_decl_timed acc se =
        let uu____8411 = acc  in
        match uu____8411 with
        | (uu____8446,uu____8447,env1,uu____8449) ->
            let uu____8462 =
              FStar_Util.record_time
                (fun uu____8508  -> process_one_decl acc se)
               in
            (match uu____8462 with
             | (r,ms_elapsed) ->
                 let uu____8571 =
                   let uu____8572 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8572
                   then
                     let uu____8573 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8574 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8573 uu____8574
                   else ()  in
                 r)
         in
      let uu____8576 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8576 with
      | (ses1,exports,env1,uu____8624) ->
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
          let uu___106_8661 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___106_8661.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___106_8661.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___106_8661.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___106_8661.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___106_8661.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___106_8661.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___106_8661.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___106_8661.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___106_8661.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___106_8661.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___106_8661.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___106_8661.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___106_8661.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___106_8661.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___106_8661.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___106_8661.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___106_8661.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___106_8661.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___106_8661.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___106_8661.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___106_8661.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___106_8661.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___106_8661.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___106_8661.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___106_8661.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___106_8661.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___106_8661.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___106_8661.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___106_8661.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___106_8661.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___106_8661.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___106_8661.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___106_8661.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___106_8661.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8675 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8675 with
          | (univs2,t1) ->
              let uu____8682 =
                let uu____8683 =
                  let uu____8684 =
                    let uu____8688 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8688  in
                  FStar_All.pipe_left uu____8684
                    (FStar_Options.Other "Exports")
                   in
                if uu____8683
                then
                  let uu____8689 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8690 =
                    let uu____8691 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8691
                      (FStar_String.concat ", ")
                     in
                  let uu____8700 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8689 uu____8690 uu____8700
                else ()  in
              let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2  in
              let uu____8703 =
                FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
              FStar_All.pipe_right uu____8703
                (fun a248  -> (Obj.magic ()) a248)
           in
        let check_term1 lid univs1 t =
          let uu____8725 =
            let uu____8726 =
              let uu____8727 =
                FStar_Syntax_Print.lid_to_string
                  modul.FStar_Syntax_Syntax.name
                 in
              let uu____8728 = FStar_Syntax_Print.lid_to_string lid  in
              FStar_Util.format2
                "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
                uu____8727 uu____8728
               in
            FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8726
             in
          let uu____8729 = check_term lid univs1 t  in
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8736) ->
              let uu____8745 =
                let uu____8746 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8746  in
              if uu____8745
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8756,uu____8757) ->
              let t =
                let uu____8769 =
                  let uu____8774 =
                    let uu____8775 =
                      let uu____8788 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8788)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8775  in
                  FStar_Syntax_Syntax.mk uu____8774  in
                uu____8769 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8795,uu____8796,uu____8797) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8805 =
                let uu____8806 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8806  in
              if uu____8805 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8810,lbs),uu____8812) ->
              let uu____8827 =
                let uu____8828 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8828  in
              if uu____8827
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
              let uu____8847 =
                let uu____8848 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8848  in
              if uu____8847
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8855 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8856 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8863 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8864 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8865 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____8866 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8873 -> ()  in
        let uu____8874 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____8874 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____8962) -> true
             | uu____8963 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8986 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____9017 ->
                   let uu____9018 =
                     let uu____9023 =
                       let uu____9024 =
                         let uu____9037 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____9037)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____9024  in
                     FStar_Syntax_Syntax.mk uu____9023  in
                   uu____9018 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____9045,uu____9046) ->
            let s1 =
              let uu___107_9056 = s  in
              let uu____9057 =
                let uu____9058 =
                  let uu____9065 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____9065)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____9058  in
              let uu____9066 =
                let uu____9069 =
                  let uu____9072 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____9072  in
                FStar_Syntax_Syntax.Assumption :: uu____9069  in
              {
                FStar_Syntax_Syntax.sigel = uu____9057;
                FStar_Syntax_Syntax.sigrng =
                  (uu___107_9056.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____9066;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___107_9056.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___107_9056.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____9075 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____9092 =
        match uu____9092 with
        | (uvs,t) ->
            let uu___108_9099 = s  in
            let uu____9100 =
              let uu____9103 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____9103  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___108_9099.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____9100;
              FStar_Syntax_Syntax.sigmeta =
                (uu___108_9099.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___108_9099.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____9117 -> failwith "Impossible!"  in
        let c_opt =
          let uu____9121 = FStar_Syntax_Util.is_unit t  in
          if uu____9121
          then
            let uu____9124 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____9124
          else
            (let uu____9126 =
               let uu____9127 = FStar_Syntax_Subst.compress t  in
               uu____9127.FStar_Syntax_Syntax.n  in
             match uu____9126 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____9132,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____9152 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____9161 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____9161
           then
             let uu____9162 =
               let uu____9163 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____9163 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____9162
           else
             (let uu____9171 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____9171))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9181 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9200 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____9217 ->
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
                            (lid,uu____9261,uu____9262,uu____9263,uu____9264,uu____9265)
                            ->
                            let uu____9274 =
                              let uu____9275 =
                                let uu____9278 =
                                  FStar_ST.op_Bang abstract_inductive_tycons
                                   in
                                lid :: uu____9278  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_tycons uu____9275
                               in
                            let uu____9379 = vals_of_abstract_inductive s1
                               in
                            FStar_List.append uu____9379 sigelts1
                        | FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____9383,uu____9384,uu____9385,uu____9386,uu____9387)
                            ->
                            let uu____9392 =
                              let uu____9393 =
                                let uu____9396 =
                                  FStar_ST.op_Bang
                                    abstract_inductive_datacons
                                   in
                                lid :: uu____9396  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_datacons uu____9393
                               in
                            sigelts1
                        | uu____9497 ->
                            failwith
                              "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                   [])
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9504 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9504
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9510 =
                   let uu___109_9511 = s  in
                   let uu____9512 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___109_9511.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___109_9511.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9512;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___109_9511.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___109_9511.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9510])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9522 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9522
            then []
            else
              (let uu____9526 = lbs  in
               match uu____9526 with
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
                       (fun uu____9582  ->
                          match uu____9582 with
                          | (uu____9589,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9607  ->
                            match uu____9607 with
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
                          (fun uu____9627  ->
                             match uu____9627 with
                             | (uu____9634,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9647,uu____9648) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9653 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9708 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                        in
                     FStar_Ident.lid_equals lid uu____9708) uu____9653
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9711 =
                   let uu___110_9712 = s  in
                   let uu____9713 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___110_9712.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___110_9712.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9713;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___110_9712.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___110_9712.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9711]
               else [])
            else
              (let uu____9718 =
                 let uu___111_9719 = s  in
                 let uu____9720 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___111_9719.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___111_9719.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9720;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___111_9719.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___111_9719.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9718])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9723 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9724 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9725 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9726 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9739 -> [s]  in
      let uu___112_9740 = m  in
      let uu____9741 =
        let uu____9742 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____9742 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___112_9740.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9741;
        FStar_Syntax_Syntax.exports =
          (uu___112_9740.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____9769 =
        let uu____9770 = FStar_Syntax_DsEnv.pop ()  in
        FStar_All.pipe_right uu____9770 (fun a249  -> (Obj.magic ()) a249)
         in
      let en = FStar_TypeChecker_Env.pop env msg  in
      let uu____9772 =
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
         in
      en
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv1 = FStar_Syntax_DsEnv.push env.FStar_TypeChecker_Env.dsenv
         in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___113_9785 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___113_9785.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___113_9785.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___113_9785.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___113_9785.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___113_9785.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___113_9785.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___113_9785.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___113_9785.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___113_9785.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___113_9785.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___113_9785.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___113_9785.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___113_9785.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___113_9785.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___113_9785.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___113_9785.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___113_9785.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___113_9785.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___113_9785.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___113_9785.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___113_9785.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___113_9785.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___113_9785.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___113_9785.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___113_9785.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___113_9785.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___113_9785.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___113_9785.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___113_9785.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___113_9785.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___113_9785.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___113_9785.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___113_9785.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___113_9785.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___113_9785.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___113_9785.FStar_TypeChecker_Env.dep_graph)
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
      let uu____9809 =
        let uu____9810 = FStar_Options.debug_any ()  in
        if uu____9810
        then
          FStar_Util.print3 "%s %s of %s\n" action label1
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
        else ()  in
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env1 =
        let uu___114_9815 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___114_9815.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___114_9815.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___114_9815.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___114_9815.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___114_9815.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___114_9815.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___114_9815.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___114_9815.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___114_9815.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___114_9815.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___114_9815.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___114_9815.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___114_9815.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___114_9815.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___114_9815.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___114_9815.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (modul.FStar_Syntax_Syntax.is_interface);
          FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
          FStar_TypeChecker_Env.lax =
            (uu___114_9815.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___114_9815.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard =
            (uu___114_9815.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___114_9815.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___114_9815.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___114_9815.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___114_9815.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___114_9815.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___114_9815.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___114_9815.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___114_9815.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___114_9815.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___114_9815.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___114_9815.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___114_9815.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___114_9815.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___114_9815.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___114_9815.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___114_9815.FStar_TypeChecker_Env.dep_graph)
        }  in
      let env2 =
        FStar_TypeChecker_Env.set_current_module env1
          modul.FStar_Syntax_Syntax.name
         in
      let uu____9817 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
         in
      match uu____9817 with
      | (ses,exports,env3) ->
          ((let uu___115_9850 = modul  in
            {
              FStar_Syntax_Syntax.name =
                (uu___115_9850.FStar_Syntax_Syntax.name);
              FStar_Syntax_Syntax.declarations = ses;
              FStar_Syntax_Syntax.exports =
                (uu___115_9850.FStar_Syntax_Syntax.exports);
              FStar_Syntax_Syntax.is_interface =
                (uu___115_9850.FStar_Syntax_Syntax.is_interface)
            }), exports, env3)
  
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
        let uu____9878 = tc_decls env decls  in
        match uu____9878 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___116_9909 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___116_9909.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___116_9909.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___116_9909.FStar_Syntax_Syntax.is_interface)
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
      let uu____9966 = tc_partial_modul env01 m  in
      match uu____9966 with
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
          let uu____10004 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____10004
          then
            let modul_iface = extract_interface en m  in
            let uu____10014 =
              let uu____10015 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low
                 in
              if uu____10015
              then
                let uu____10016 =
                  let uu____10017 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10017 then "" else " (in lax mode) "  in
                let uu____10019 =
                  let uu____10020 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10020
                  then
                    let uu____10021 =
                      let uu____10022 = FStar_Syntax_Print.modul_to_string m
                         in
                      Prims.strcat uu____10022 "\n"  in
                    Prims.strcat "\nfrom: " uu____10021
                  else ""  in
                let uu____10024 =
                  let uu____10025 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  if uu____10025
                  then
                    let uu____10026 =
                      let uu____10027 =
                        FStar_Syntax_Print.modul_to_string modul_iface  in
                      Prims.strcat uu____10027 "\n"  in
                    Prims.strcat "\nto: " uu____10026
                  else ""  in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____10016
                  uu____10019 uu____10024
              else ()  in
            let en0 =
              let en0 =
                pop_context en
                  (Prims.strcat "Ending modul "
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              let en01 =
                let uu___117_10033 = en0  in
                let uu____10034 =
                  let uu____10047 =
                    FStar_All.pipe_right
                      en.FStar_TypeChecker_Env.qtbl_name_and_index
                      FStar_Pervasives_Native.fst
                     in
                  (uu____10047, FStar_Pervasives_Native.None)  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___117_10033.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___117_10033.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___117_10033.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___117_10033.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___117_10033.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___117_10033.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___117_10033.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___117_10033.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___117_10033.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___117_10033.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___117_10033.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___117_10033.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___117_10033.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___117_10033.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___117_10033.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___117_10033.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___117_10033.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___117_10033.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___117_10033.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___117_10033.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___117_10033.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___117_10033.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___117_10033.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___117_10033.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___117_10033.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___117_10033.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___117_10033.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index = uu____10034;
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___117_10033.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___117_10033.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___117_10033.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___117_10033.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___117_10033.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___117_10033.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___117_10033.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___117_10033.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___117_10033.FStar_TypeChecker_Env.dep_graph)
                }  in
              let uu____10084 =
                let uu____10085 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____10085  in
              if uu____10084
              then
                let uu____10086 =
                  let uu____10087 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____10087
                    (fun a250  -> (Obj.magic ()) a250)
                   in
                z3_reset_options en01
              else en01  in
            let uu____10089 = tc_modul en0 modul_iface  in
            match uu____10089 with
            | (modul_iface1,must_be_none,env) ->
                (if must_be_none <> FStar_Pervasives_Native.None
                 then
                   failwith
                     "Impossible! finish_partial_module: expected the second component to be None"
                 else
                   (((let uu___118_10135 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___118_10135.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___118_10135.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___118_10135.FStar_Syntax_Syntax.is_interface)
                      })), (FStar_Pervasives_Native.Some modul_iface1), env))
          else
            (let modul =
               let uu____10138 = FStar_Options.use_extracted_interfaces ()
                  in
               if uu____10138
               then
                 let uu___119_10139 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___119_10139.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___119_10139.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___119_10139.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___120_10141 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___120_10141.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___120_10141.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___120_10141.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             let uu____10143 =
               let uu____10144 =
                 FStar_All.pipe_right
                   env.FStar_TypeChecker_Env.qtbl_name_and_index
                   FStar_Pervasives_Native.fst
                  in
               FStar_All.pipe_right uu____10144 FStar_Util.smap_clear  in
             let uu____10171 =
               let uu____10172 =
                 ((let uu____10175 = FStar_Options.lax ()  in
                   Prims.op_Negation uu____10175) &&
                    (let uu____10177 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____10177))
                   && (Prims.op_Negation loading_from_cache)
                  in
               if uu____10172 then check_exports env modul exports else ()
                in
             let uu____10179 =
               let uu____10180 =
                 pop_context env
                   (Prims.strcat "Ending modul "
                      (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                  in
               FStar_All.pipe_right uu____10180
                 (fun a251  -> (Obj.magic ()) a251)
                in
             let uu____10181 =
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul
                in
             let uu____10182 =
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
                in
             let uu____10183 =
               let uu____10184 =
                 let uu____10185 = FStar_Options.interactive ()  in
                 Prims.op_Negation uu____10185  in
               if uu____10184
               then
                 let uu____10186 =
                   FStar_Options.restore_cmd_line_options true  in
                 FStar_All.pipe_right uu____10186
                   (fun a252  -> (Obj.magic ()) a252)
               else ()  in
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
        let uu____10202 =
          let uu____10203 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____10203  in
        push_context env uu____10202  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               let uu____10216 =
                 FStar_All.pipe_right lids
                   (FStar_List.iter
                      (fun lid  ->
                         let uu____10222 =
                           FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                         ()))
                  in
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____10233 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____10233 with | (uu____10242,uu____10243,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      let uu____10267 =
        let uu____10268 = FStar_Options.debug_any ()  in
        if uu____10268
        then
          let uu____10269 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.print2 "Checking %s: %s\n"
            (if m.FStar_Syntax_Syntax.is_interface
             then "i'face"
             else "module") uu____10269
        else ()  in
      let env1 =
        let uu___121_10273 = env  in
        let uu____10274 =
          let uu____10275 =
            FStar_Options.should_verify
              (m.FStar_Syntax_Syntax.name).FStar_Ident.str
             in
          Prims.op_Negation uu____10275  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___121_10273.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___121_10273.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___121_10273.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___121_10273.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___121_10273.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___121_10273.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___121_10273.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___121_10273.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___121_10273.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___121_10273.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___121_10273.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___121_10273.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___121_10273.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___121_10273.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___121_10273.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___121_10273.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___121_10273.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___121_10273.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax = uu____10274;
          FStar_TypeChecker_Env.lax_universes =
            (uu___121_10273.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard =
            (uu___121_10273.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___121_10273.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___121_10273.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___121_10273.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___121_10273.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___121_10273.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___121_10273.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___121_10273.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___121_10273.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___121_10273.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___121_10273.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___121_10273.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___121_10273.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___121_10273.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___121_10273.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___121_10273.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___121_10273.FStar_TypeChecker_Env.dep_graph)
        }  in
      let uu____10276 = tc_modul env1 m  in
      match uu____10276 with
      | (m1,m_iface_opt,env2) ->
          let uu____10300 =
            let uu____10301 =
              FStar_Options.dump_module
                (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10301
            then
              let uu____10302 = FStar_Syntax_Print.modul_to_string m1  in
              FStar_Util.print1 "Module after type checking:\n%s\n"
                uu____10302
            else ()  in
          let uu____10304 =
            let uu____10305 =
              (FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                &&
                (FStar_Options.debug_at_level
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                   (FStar_Options.Other "Normalize"))
               in
            if uu____10305
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
                      let uu____10340 =
                        FStar_Syntax_Subst.open_univ_vars
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      match uu____10340 with
                      | (univnames1,e) ->
                          let uu___122_10347 = lb  in
                          let uu____10348 =
                            let uu____10351 =
                              FStar_TypeChecker_Env.push_univ_vars env2
                                univnames1
                               in
                            n1 uu____10351 e  in
                          {
                            FStar_Syntax_Syntax.lbname =
                              (uu___122_10347.FStar_Syntax_Syntax.lbname);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___122_10347.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___122_10347.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___122_10347.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef = uu____10348;
                            FStar_Syntax_Syntax.lbattrs =
                              (uu___122_10347.FStar_Syntax_Syntax.lbattrs);
                            FStar_Syntax_Syntax.lbpos =
                              (uu___122_10347.FStar_Syntax_Syntax.lbpos)
                          }
                       in
                    let uu___123_10352 = se  in
                    let uu____10353 =
                      let uu____10354 =
                        let uu____10361 =
                          let uu____10368 = FStar_List.map update lbs  in
                          (b, uu____10368)  in
                        (uu____10361, ids)  in
                      FStar_Syntax_Syntax.Sig_let uu____10354  in
                    {
                      FStar_Syntax_Syntax.sigel = uu____10353;
                      FStar_Syntax_Syntax.sigrng =
                        (uu___123_10352.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___123_10352.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___123_10352.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___123_10352.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10381 -> se  in
              let normalized_module =
                let uu___124_10383 = m1  in
                let uu____10384 =
                  FStar_List.map normalize_toplevel_lets
                    m1.FStar_Syntax_Syntax.declarations
                   in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___124_10383.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = uu____10384;
                  FStar_Syntax_Syntax.exports =
                    (uu___124_10383.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___124_10383.FStar_Syntax_Syntax.is_interface)
                }  in
              let uu____10385 =
                FStar_Syntax_Print.modul_to_string normalized_module  in
              FStar_Util.print1 "%s\n" uu____10385
            else ()  in
          (m1, m_iface_opt, env2)
  