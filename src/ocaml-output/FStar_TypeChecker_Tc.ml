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
          let uu___93_54 = env  in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid  in (lid, uu____80)  in
              FStar_Pervasives_Native.Some uu____75  in
            (tbl, uu____68)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___93_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___93_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___93_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___93_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___93_54.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___93_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___93_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___93_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___93_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___93_54.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___93_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___93_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___93_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___93_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___93_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___93_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___93_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___93_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___93_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___93_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___93_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___93_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___93_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___93_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___93_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___93_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___93_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___93_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___93_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___93_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___93_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___93_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___93_54.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___93_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___93_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___93_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___93_54.FStar_TypeChecker_Env.dep_graph)
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
          let uu___94_104 = env  in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid  in (lid, uu____130)
                 in
              FStar_Pervasives_Native.Some uu____125  in
            (tbl, uu____118)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___94_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___94_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___94_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___94_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___94_104.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___94_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___94_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___94_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___94_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___94_104.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___94_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___94_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___94_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___94_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___94_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___94_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___94_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___94_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___94_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___94_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___94_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___94_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___94_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___94_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___94_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___94_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___94_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___94_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___94_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___94_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___94_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___94_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___94_104.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___94_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___94_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___94_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___94_104.FStar_TypeChecker_Env.dep_graph)
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
                           let uu___95_456 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___95_456.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___95_456.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___95_456.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___95_456.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___95_456.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___95_456.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___95_456.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___95_456.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___95_456.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___95_456.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___95_456.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___95_456.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___95_456.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___95_456.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___95_456.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___95_456.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___95_456.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___95_456.FStar_Syntax_Syntax.eff_attrs)
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
                               let uu___96_547 = ed1  in
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
                                      let uu___97_580 = a  in
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
                                          (uu___97_580.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___97_580.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___97_580.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___97_580.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____581;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____593
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___96_547.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___96_547.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___96_547.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___96_547.FStar_Syntax_Syntax.signature);
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
                                   (uu___96_547.FStar_Syntax_Syntax.eff_attrs)
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
                                    let uu____908 =
                                      let uu____915 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____920 =
                                        let uu____927 =
                                          let uu____932 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____932
                                           in
                                        [uu____927]  in
                                      uu____915 :: uu____920  in
                                    let uu____945 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____908
                                      uu____945
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____957 = fresh_effect_signature ()
                                     in
                                  match uu____957 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____981 =
                                          let uu____988 =
                                            let uu____993 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____993
                                             in
                                          [uu____988]  in
                                        let uu____1002 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____981
                                          uu____1002
                                         in
                                      let expected_k =
                                        let uu____1008 =
                                          let uu____1015 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____1020 =
                                            let uu____1027 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1032 =
                                              let uu____1039 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____1044 =
                                                let uu____1051 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1056 =
                                                  let uu____1063 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____1063]  in
                                                uu____1051 :: uu____1056  in
                                              uu____1039 :: uu____1044  in
                                            uu____1027 :: uu____1032  in
                                          uu____1015 :: uu____1020  in
                                        let uu____1092 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1008
                                          uu____1092
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____1105 =
                                      let uu____1108 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1108
                                       in
                                    let uu____1109 =
                                      let uu____1110 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1110
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1105
                                      uu____1109
                                     in
                                  let expected_k =
                                    let uu____1122 =
                                      let uu____1129 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1134 =
                                        let uu____1141 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____1146 =
                                          let uu____1153 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____1158 =
                                            let uu____1165 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1165]  in
                                          uu____1153 :: uu____1158  in
                                        uu____1141 :: uu____1146  in
                                      uu____1129 :: uu____1134  in
                                    let uu____1190 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1122
                                      uu____1190
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1205 =
                                      let uu____1212 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1217 =
                                        let uu____1224 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1224]  in
                                      uu____1212 :: uu____1217  in
                                    let uu____1241 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1205
                                      uu____1241
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____1253 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1253 with
                                  | (t,uu____1267) ->
                                      let expected_k =
                                        let uu____1271 =
                                          let uu____1278 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1283 =
                                            let uu____1290 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____1295 =
                                              let uu____1302 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____1302]  in
                                            uu____1290 :: uu____1295  in
                                          uu____1278 :: uu____1283  in
                                        let uu____1323 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____1271
                                          uu____1323
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____1336 =
                                      let uu____1339 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1339
                                       in
                                    let uu____1340 =
                                      let uu____1341 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1341
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1336
                                      uu____1340
                                     in
                                  let b_wp_a =
                                    let uu____1353 =
                                      let uu____1360 =
                                        let uu____1365 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1365
                                         in
                                      [uu____1360]  in
                                    let uu____1374 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1353
                                      uu____1374
                                     in
                                  let expected_k =
                                    let uu____1380 =
                                      let uu____1387 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1392 =
                                        let uu____1399 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1404 =
                                          let uu____1411 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1411]  in
                                        uu____1399 :: uu____1404  in
                                      uu____1387 :: uu____1392  in
                                    let uu____1432 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1380
                                      uu____1432
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1447 =
                                      let uu____1454 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1459 =
                                        let uu____1466 =
                                          let uu____1471 =
                                            let uu____1472 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1472
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1471
                                           in
                                        let uu____1481 =
                                          let uu____1488 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1488]  in
                                        uu____1466 :: uu____1481  in
                                      uu____1454 :: uu____1459  in
                                    let uu____1509 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1447
                                      uu____1509
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1524 =
                                      let uu____1531 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1536 =
                                        let uu____1543 =
                                          let uu____1548 =
                                            let uu____1549 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1549
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1548
                                           in
                                        let uu____1558 =
                                          let uu____1565 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1565]  in
                                        uu____1543 :: uu____1558  in
                                      uu____1531 :: uu____1536  in
                                    let uu____1586 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1524
                                      uu____1586
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1601 =
                                      let uu____1608 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1608]  in
                                    let uu____1621 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1601
                                      uu____1621
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1633 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1633 with
                                  | (t,uu____1647) ->
                                      let expected_k =
                                        let uu____1651 =
                                          let uu____1658 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1663 =
                                            let uu____1670 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1670]  in
                                          uu____1658 :: uu____1663  in
                                        let uu____1687 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1651
                                          uu____1687
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1690 =
                                  let uu____1717 =
                                    let uu____1718 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1718.FStar_Syntax_Syntax.n  in
                                  match uu____1717 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1765 ->
                                      let repr =
                                        let uu____1767 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1767 with
                                        | (t,uu____1773) ->
                                            let expected_k =
                                              let uu____1777 =
                                                let uu____1784 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1789 =
                                                  let uu____1796 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1796]  in
                                                uu____1784 :: uu____1789  in
                                              let uu____1813 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1777 uu____1813
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
                                        let uu____1830 =
                                          let uu____1837 =
                                            let uu____1838 =
                                              let uu____1853 =
                                                let uu____1862 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1869 =
                                                  let uu____1878 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1878]  in
                                                uu____1862 :: uu____1869  in
                                              (repr1, uu____1853)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1838
                                             in
                                          FStar_Syntax_Syntax.mk uu____1837
                                           in
                                        uu____1830
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1929 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1929 wp  in
                                      let destruct_repr t =
                                        let uu____1944 =
                                          let uu____1945 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1945.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1944 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1956,(t1,uu____1958)::
                                             (wp,uu____1960)::[])
                                            -> (t1, wp)
                                        | uu____2003 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____2022 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____2022
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____2023 =
                                          fresh_effect_signature ()  in
                                        match uu____2023 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____2047 =
                                                let uu____2054 =
                                                  let uu____2059 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____2059
                                                   in
                                                [uu____2054]  in
                                              let uu____2068 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2047 uu____2068
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
                                              let uu____2074 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____2074
                                               in
                                            let wp_g_x =
                                              let uu____2078 =
                                                let uu____2083 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____2084 =
                                                  let uu____2085 =
                                                    let uu____2092 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2092
                                                     in
                                                  [uu____2085]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____2083 uu____2084
                                                 in
                                              uu____2078
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____2119 =
                                                  let uu____2124 =
                                                    let uu____2125 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2125
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____2134 =
                                                    let uu____2135 =
                                                      let uu____2138 =
                                                        let uu____2141 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____2142 =
                                                          let uu____2145 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____2146 =
                                                            let uu____2149 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____2150 =
                                                              let uu____2153
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____2153]
                                                               in
                                                            uu____2149 ::
                                                              uu____2150
                                                             in
                                                          uu____2145 ::
                                                            uu____2146
                                                           in
                                                        uu____2141 ::
                                                          uu____2142
                                                         in
                                                      r :: uu____2138  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2135
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2124 uu____2134
                                                   in
                                                uu____2119
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____2169 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____2169
                                              then
                                                let uu____2176 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____2181 =
                                                  let uu____2188 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____2188]  in
                                                uu____2176 :: uu____2181
                                              else []  in
                                            let expected_k =
                                              let uu____2213 =
                                                let uu____2220 =
                                                  let uu____2227 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____2232 =
                                                    let uu____2239 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____2239]  in
                                                  uu____2227 :: uu____2232
                                                   in
                                                let uu____2256 =
                                                  let uu____2263 =
                                                    let uu____2270 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____2275 =
                                                      let uu____2282 =
                                                        let uu____2287 =
                                                          let uu____2288 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____2288
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____2287
                                                         in
                                                      let uu____2289 =
                                                        let uu____2296 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____2301 =
                                                          let uu____2308 =
                                                            let uu____2313 =
                                                              let uu____2314
                                                                =
                                                                let uu____2321
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____2321]
                                                                 in
                                                              let uu____2334
                                                                =
                                                                let uu____2337
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____2337
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____2314
                                                                uu____2334
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2313
                                                             in
                                                          [uu____2308]  in
                                                        uu____2296 ::
                                                          uu____2301
                                                         in
                                                      uu____2282 ::
                                                        uu____2289
                                                       in
                                                    uu____2270 :: uu____2275
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____2263
                                                   in
                                                FStar_List.append uu____2220
                                                  uu____2256
                                                 in
                                              let uu____2368 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2213 uu____2368
                                               in
                                            let uu____2371 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____2371 with
                                             | (expected_k1,uu____2387,uu____2388)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___98_2395 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_sig
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.gamma_sig);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___98_2395.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____2415 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____2415
                                           in
                                        let res =
                                          let wp =
                                            let uu____2422 =
                                              let uu____2427 =
                                                let uu____2428 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2428
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____2437 =
                                                let uu____2438 =
                                                  let uu____2441 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____2442 =
                                                    let uu____2445 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____2445]  in
                                                  uu____2441 :: uu____2442
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____2438
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____2427 uu____2437
                                               in
                                            uu____2422
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____2457 =
                                            let uu____2464 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____2469 =
                                              let uu____2476 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____2476]  in
                                            uu____2464 :: uu____2469  in
                                          let uu____2493 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____2457
                                            uu____2493
                                           in
                                        let uu____2496 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____2496 with
                                        | (expected_k1,uu____2512,uu____2513)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____2519 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____2519 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____2558 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____2579 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____2591 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____2591 with
                                               | (usubst,uvs) ->
                                                   let uu____2614 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____2615 =
                                                     let uu___99_2616 = act
                                                        in
                                                     let uu____2617 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____2618 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____2619 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___99_2616.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___99_2616.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____2617;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____2618;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____2619
                                                     }  in
                                                   (uu____2614, uu____2615))
                                             in
                                          match uu____2579 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____2623 =
                                                  let uu____2624 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____2624.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____2623 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____2646 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____2646
                                                    then
                                                      let uu____2647 =
                                                        let uu____2650 =
                                                          let uu____2651 =
                                                            let uu____2652 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2652
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____2651
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____2650
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____2647
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____2668 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____2669 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____2669 with
                                               | (act_typ1,uu____2677,g_t) ->
                                                   let env' =
                                                     let uu___100_2680 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___100_2680.FStar_TypeChecker_Env.dep_graph)
                                                     }  in
                                                   ((let uu____2682 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____2682
                                                     then
                                                       let uu____2683 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____2684 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____2685 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____2683
                                                         uu____2684
                                                         uu____2685
                                                     else ());
                                                    (let uu____2687 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____2687 with
                                                     | (act_defn,uu____2695,g_a)
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
                                                         let uu____2699 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____2727
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____2727
                                                                with
                                                                | (bs1,uu____2737)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____2744
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2744
                                                                     in
                                                                    let uu____2747
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____2747
                                                                    with
                                                                    | 
                                                                    (k1,uu____2759,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____2761 ->
                                                               let uu____2762
                                                                 =
                                                                 let uu____2767
                                                                   =
                                                                   let uu____2768
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____2769
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____2768
                                                                    uu____2769
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____2767)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____2762
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____2699
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____2778
                                                                  =
                                                                  let uu____2779
                                                                    =
                                                                    let uu____2780
                                                                    =
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_k
                                                                    uu____2780
                                                                     in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g_a
                                                                    uu____2779
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____2778);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____2782
                                                                    =
                                                                    let uu____2783
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____2783.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____2782
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____2804
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____2804
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____2811
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____2811
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____2831
                                                                    =
                                                                    let uu____2832
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____2832]
                                                                     in
                                                                    let uu____2833
                                                                    =
                                                                    let uu____2842
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____2842]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2831;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2833;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____2861
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2861))
                                                                  | uu____2864
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____2865
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
                                                                    let uu____2885
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____2885))
                                                                   in
                                                                match uu____2865
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
                                                                    let uu___101_2898
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___101_2898.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___101_2898.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___101_2898.FStar_Syntax_Syntax.action_params);
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
                                match uu____1690 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____2964 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____2964
                                       in
                                    let uu____2967 =
                                      let uu____2976 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____2976 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____3007 ->
                                               let uu____3010 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____3016 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____3016 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____3010
                                               then (gen_univs, t)
                                               else
                                                 (let uu____3030 =
                                                    let uu____3035 =
                                                      let uu____3036 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____3037 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____3036 uu____3037
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____3035)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____3030
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____2967 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____3057 =
                                             let uu____3068 =
                                               let uu____3069 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____3069.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____3068)  in
                                           match uu____3057 with
                                           | ([],uu____3078) -> t
                                           | (uu____3089,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____3090,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____3120 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____3144 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____3144
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____3151 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____3153 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____3153))
                                                && (m <> n1)
                                               in
                                            if uu____3151
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____3171 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____3178 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____3179 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____3171 uu____3178
                                                  uu____3179
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____3191 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____3191 with
                                           | (univs2,defn) ->
                                               let uu____3206 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____3206 with
                                                | (univs',typ) ->
                                                    let uu___102_3222 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___102_3222.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___102_3222.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___102_3222.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___103_3225 = ed2  in
                                           let uu____3226 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____3227 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____3228 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____3229 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____3230 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____3231 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____3232 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____3233 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____3234 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____3235 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____3236 =
                                             let uu____3237 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____3237
                                              in
                                           let uu____3254 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____3255 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____3256 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___103_3225.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___103_3225.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____3226;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____3227;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____3228;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____3229;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____3230;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____3231;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____3232;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____3233;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____3234;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____3235;
                                             FStar_Syntax_Syntax.repr =
                                               uu____3236;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____3254;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____3255;
                                             FStar_Syntax_Syntax.actions =
                                               uu____3256;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___103_3225.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____3260 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____3260
                                           then
                                             let uu____3261 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____3261
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
      let uu____3283 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____3283 with
      | (effect_binders_un,signature_un) ->
          let uu____3300 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3300 with
           | (effect_binders,env1,uu____3319) ->
               let uu____3320 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3320 with
                | (signature,uu____3336) ->
                    let raise_error1 uu____3351 =
                      match uu____3351 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3377  ->
                           match uu____3377 with
                           | (bv,qual) ->
                               let uu____3388 =
                                 let uu___104_3389 = bv  in
                                 let uu____3390 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___104_3389.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___104_3389.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3390
                                 }  in
                               (uu____3388, qual)) effect_binders
                       in
                    let uu____3393 =
                      let uu____3400 =
                        let uu____3401 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3401.FStar_Syntax_Syntax.n  in
                      match uu____3400 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3411)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3433 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3393 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3457 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3457
                           then
                             let uu____3458 =
                               let uu____3461 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3461  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3458
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3501 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3501 with
                           | (t2,comp,uu____3514) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3523 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____3523 with
                          | (repr,_comp) ->
                              ((let uu____3545 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3545
                                then
                                  let uu____3546 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3546
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
                                let uu____3550 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____3552 =
                                    let uu____3553 =
                                      let uu____3554 =
                                        let uu____3569 =
                                          let uu____3578 =
                                            let uu____3585 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____3588 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____3585, uu____3588)  in
                                          [uu____3578]  in
                                        (wp_type, uu____3569)  in
                                      FStar_Syntax_Syntax.Tm_app uu____3554
                                       in
                                    mk1 uu____3553  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____3552
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____3623 =
                                      let uu____3628 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____3628)  in
                                    let uu____3629 =
                                      let uu____3636 =
                                        let uu____3641 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____3641
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____3636]  in
                                    uu____3623 :: uu____3629  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____3667 =
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
                                  let uu____3726 = item  in
                                  match uu____3726 with
                                  | (u_item,item1) ->
                                      let uu____3741 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____3741 with
                                       | (item2,item_comp) ->
                                           ((let uu____3757 =
                                               let uu____3758 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____3758
                                                in
                                             if uu____3757
                                             then
                                               let uu____3759 =
                                                 let uu____3764 =
                                                   let uu____3765 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____3766 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____3765 uu____3766
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____3764)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____3759
                                             else ());
                                            (let uu____3768 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____3768 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____3786 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____3787 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____3788 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____3788 with
                                | (dmff_env1,uu____3812,bind_wp,bind_elab) ->
                                    let uu____3815 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____3815 with
                                     | (dmff_env2,uu____3839,return_wp,return_elab)
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
                                           let uu____3848 =
                                             let uu____3849 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____3849.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3848 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____3895 =
                                                 let uu____3910 =
                                                   let uu____3915 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____3915
                                                    in
                                                 match uu____3910 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____3973 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____3895 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____4014 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4014 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4031 =
                                                          let uu____4032 =
                                                            let uu____4047 =
                                                              let uu____4056
                                                                =
                                                                let uu____4063
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____4066
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4063,
                                                                  uu____4066)
                                                                 in
                                                              [uu____4056]
                                                               in
                                                            (wp_type,
                                                              uu____4047)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4032
                                                           in
                                                        mk1 uu____4031  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____4091 =
                                                      let uu____4100 =
                                                        let uu____4101 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4101
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4100
                                                       in
                                                    (match uu____4091 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____4124
                                                           =
                                                           let error_msg =
                                                             let uu____4126 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____4127 =
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
                                                               uu____4126
                                                               uu____4127
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
                                                               ((let uu____4132
                                                                   =
                                                                   let uu____4133
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____4133
                                                                    in
                                                                 if
                                                                   uu____4132
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4135
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
                                                                   uu____4135
                                                                   (fun a238 
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
                                                             let uu____4160 =
                                                               let uu____4165
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____4166
                                                                 =
                                                                 let uu____4167
                                                                   =
                                                                   let uu____4174
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____4174,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____4167]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4165
                                                                 uu____4166
                                                                in
                                                             uu____4160
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____4201 =
                                                             let uu____4202 =
                                                               let uu____4209
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4209]
                                                                in
                                                             b11 ::
                                                               uu____4202
                                                              in
                                                           let uu____4226 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____4201
                                                             uu____4226
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4229 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4235 =
                                             let uu____4236 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4236.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4235 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4282 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4282
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4297 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4303 =
                                             let uu____4304 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4304.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4303 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____4333 =
                                                 let uu____4334 =
                                                   let uu____4341 =
                                                     let uu____4346 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4346
                                                      in
                                                   [uu____4341]  in
                                                 FStar_List.append uu____4334
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____4333 body what
                                           | uu____4359 ->
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
                                             (let uu____4382 =
                                                let uu____4383 =
                                                  let uu____4384 =
                                                    let uu____4399 =
                                                      let uu____4408 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4408
                                                       in
                                                    (t, uu____4399)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4384
                                                   in
                                                mk1 uu____4383  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4382)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4450 = f a2  in
                                               [uu____4450]
                                           | x::xs ->
                                               let uu____4455 =
                                                 apply_last1 f xs  in
                                               x :: uu____4455
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
                                           let uu____4481 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____4481 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____4511 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____4511
                                                 then
                                                   let uu____4512 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____4512
                                                 else ());
                                                (let uu____4514 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____4514))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____4523 =
                                                 let uu____4528 = mk_lid name
                                                    in
                                                 let uu____4529 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____4528 uu____4529
                                                  in
                                               (match uu____4523 with
                                                | (sigelt,fv) ->
                                                    ((let uu____4533 =
                                                        let uu____4536 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____4536
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____4533);
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
                                          (let uu____4641 =
                                             let uu____4644 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____4645 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____4644 :: uu____4645  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____4641);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____4751 =
                                               let uu____4754 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____4755 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____4754 :: uu____4755  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____4751);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____4858 =
                                                FStar_List.fold_left
                                                  (fun uu____4898  ->
                                                     fun action  ->
                                                       match uu____4898 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____4919 =
                                                             let uu____4926 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____4926
                                                               params_un
                                                              in
                                                           (match uu____4919
                                                            with
                                                            | (action_params,env',uu____4935)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____4955
                                                                     ->
                                                                    match uu____4955
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____4966
                                                                    =
                                                                    let uu___105_4967
                                                                    = bv  in
                                                                    let uu____4968
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___105_4967.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___105_4967.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____4968
                                                                    }  in
                                                                    (uu____4966,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____4972
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____4972
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
                                                                    uu____5008
                                                                    ->
                                                                    let uu____5009
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5009
                                                                     in
                                                                    ((
                                                                    let uu____5013
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____5013
                                                                    then
                                                                    let uu____5014
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____5015
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____5016
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5017
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5014
                                                                    uu____5015
                                                                    uu____5016
                                                                    uu____5017
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
                                                                    let uu____5021
                                                                    =
                                                                    let uu____5024
                                                                    =
                                                                    let uu___106_5025
                                                                    = action
                                                                     in
                                                                    let uu____5026
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____5027
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___106_5025.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___106_5025.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___106_5025.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5026;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5027
                                                                    }  in
                                                                    uu____5024
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____5021))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____4858 with
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
                                                      let uu____5066 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____5071 =
                                                        let uu____5078 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____5078]  in
                                                      uu____5066 ::
                                                        uu____5071
                                                       in
                                                    let uu____5095 =
                                                      let uu____5098 =
                                                        let uu____5099 =
                                                          let uu____5100 =
                                                            let uu____5115 =
                                                              let uu____5124
                                                                =
                                                                let uu____5131
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____5134
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____5131,
                                                                  uu____5134)
                                                                 in
                                                              [uu____5124]
                                                               in
                                                            (repr,
                                                              uu____5115)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5100
                                                           in
                                                        mk1 uu____5099  in
                                                      let uu____5159 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____5098
                                                        uu____5159
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____5095
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____5160 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____5162 =
                                                    let uu____5171 =
                                                      let uu____5172 =
                                                        let uu____5175 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____5175
                                                         in
                                                      uu____5172.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5171 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____5189)
                                                        ->
                                                        let uu____5218 =
                                                          let uu____5235 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____5235
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____5287 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____5218
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____5339 =
                                                               let uu____5340
                                                                 =
                                                                 let uu____5343
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5343
                                                                  in
                                                               uu____5340.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____5339
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____5372
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____5372
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____5387
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5412
                                                                     ->
                                                                    match uu____5412
                                                                    with
                                                                    | 
                                                                    (bv,uu____5418)
                                                                    ->
                                                                    let uu____5419
                                                                    =
                                                                    let uu____5420
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5420
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5419
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____5387
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
                                                                    let uu____5486
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____5486
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____5491
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____5499
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____5499
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____5504
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____5507
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____5504,
                                                                    uu____5507)))
                                                              | uu____5518 ->
                                                                  let uu____5519
                                                                    =
                                                                    let uu____5524
                                                                    =
                                                                    let uu____5525
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____5525
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____5524)
                                                                     in
                                                                  raise_error1
                                                                    uu____5519))
                                                    | uu____5534 ->
                                                        let uu____5535 =
                                                          let uu____5540 =
                                                            let uu____5541 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____5541
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____5540)
                                                           in
                                                        raise_error1
                                                          uu____5535
                                                     in
                                                  (match uu____5162 with
                                                   | (pre,post) ->
                                                       ((let uu____5571 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____5573 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____5575 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___107_5577
                                                             = ed  in
                                                           let uu____5578 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____5579 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____5580 =
                                                             let uu____5581 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____5581)
                                                              in
                                                           let uu____5588 =
                                                             let uu____5589 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____5589)
                                                              in
                                                           let uu____5596 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____5597 =
                                                             let uu____5598 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____5598)
                                                              in
                                                           let uu____5605 =
                                                             let uu____5606 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____5606)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____5578;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____5579;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____5580;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____5588;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____5596;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____5597;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____5605;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___107_5577.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____5613 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____5613
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____5631
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____5631
                                                               then
                                                                 let uu____5632
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____5632
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
                                                                    let uu____5645
                                                                    =
                                                                    let uu____5648
                                                                    =
                                                                    let uu____5649
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____5649)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5648
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
                                                                    uu____5645;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____5656
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____5656
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____5658
                                                                 =
                                                                 let uu____5661
                                                                   =
                                                                   let uu____5664
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____5664
                                                                    in
                                                                 FStar_List.append
                                                                   uu____5661
                                                                   sigelts'
                                                                  in
                                                               (uu____5658,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____5730 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____5730 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____5765 = FStar_List.hd ses  in
            uu____5765.FStar_Syntax_Syntax.sigrng  in
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
           | uu____5770 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____5774,[],t,uu____5776,uu____5777);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____5779;
               FStar_Syntax_Syntax.sigattrs = uu____5780;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____5782,_t_top,_lex_t_top,_0_17,uu____5785);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____5787;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____5788;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____5790,_t_cons,_lex_t_cons,_0_18,uu____5793);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____5795;
                 FStar_Syntax_Syntax.sigattrs = uu____5796;_}::[]
               when
               ((_0_17 = (Prims.parse_int "0")) &&
                  (_0_18 = (Prims.parse_int "0")))
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
                 let uu____5841 =
                   let uu____5848 =
                     let uu____5849 =
                       let uu____5856 =
                         let uu____5859 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____5859
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____5856, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____5849  in
                   FStar_Syntax_Syntax.mk uu____5848  in
                 uu____5841 FStar_Pervasives_Native.None r1  in
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
                   let uu____5875 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5875
                    in
                 let hd1 =
                   let uu____5877 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5877
                    in
                 let tl1 =
                   let uu____5879 =
                     let uu____5880 =
                       let uu____5887 =
                         let uu____5888 =
                           let uu____5895 =
                             let uu____5898 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____5898
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____5895, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____5888  in
                       FStar_Syntax_Syntax.mk uu____5887  in
                     uu____5880 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____5879
                    in
                 let res =
                   let uu____5907 =
                     let uu____5914 =
                       let uu____5915 =
                         let uu____5922 =
                           let uu____5925 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____5925
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____5922,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____5915  in
                     FStar_Syntax_Syntax.mk uu____5914  in
                   uu____5907 FStar_Pervasives_Native.None r2  in
                 let uu____5931 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____5931
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
               let uu____5954 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____5954;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____5959 ->
               let err_msg =
                 let uu____5963 =
                   let uu____5964 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____5964  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____5963
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
        let uu____5985 = FStar_Syntax_Util.type_u ()  in
        match uu____5985 with
        | (k,uu____5991) ->
            let phi1 =
              let uu____5995 = tc_check_trivial_guard env1 phi k  in
              FStar_All.pipe_right uu____5995
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
          let uu____6038 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____6038 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____6069 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas
                   in
                FStar_All.pipe_right uu____6069 FStar_List.flatten  in
              ((let uu____6083 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____6085 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     Prims.op_Negation uu____6085)
                   in
                if uu____6083
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
                          let uu____6096 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____6106,uu____6107,uu____6108,uu____6109,uu____6110)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____6119 -> failwith "Impossible!"  in
                          match uu____6096 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____6132 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____6136,uu____6137,uu____6138,uu____6139,uu____6140)
                        -> lid
                    | uu____6149 -> failwith "Impossible"  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let res =
                  let uu____6162 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____6162
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
                (let uu____6185 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____6192 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____6192 en  in
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
      | uu____6422 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____6470 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____6470 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____6489 .
    'Auu____6489 FStar_Pervasives_Native.option -> 'Auu____6489 Prims.list
  =
  fun uu___87_6498  ->
    match uu___87_6498 with
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
      | uu____6542 ->
          let rec collect1 l =
            match l with
            | [] -> []
            | hd1::tl1 ->
                let uu____6574 = collect1 tl1  in
                (match uu____6574 with
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
            | ((e,n1)::uu____6759,[]) ->
                FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
            | ([],(e,n1)::uu____6794) ->
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
      (let uu____6968 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____6968
       then
         let uu____6969 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____6969
       else ());
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let uu____6972 = get_fail_se se  in
       match uu____6972 with
       | FStar_Pervasives_Native.Some (uu____6989,false ) when
           let uu____7000 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____7000 -> ([], [])
       | FStar_Pervasives_Native.Some (errnos,uu____7006) ->
           ((let uu____7018 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____7018
             then
               let uu____7019 =
                 let uu____7020 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____7020
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____7019
             else ());
            (let errs =
               FStar_Errors.catch_errors
                 (fun uu____7038  -> tc_decl' env1 se)
                in
             (let uu____7040 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7040
              then
                (FStar_Util.print_string ">> Got issues:\n";
                 FStar_List.iter FStar_Errors.print_issue errs;
                 FStar_Util.print_string ">> //Got issues:\n")
              else ());
             (let uu____7044 =
                let uu____7059 =
                  let uu____7068 =
                    FStar_List.concatMap
                      (fun i  -> list_of_option i.FStar_Errors.issue_number)
                      errs
                     in
                  check_multi_contained errnos uu____7068  in
                (errs, uu____7059)  in
              match uu____7044 with
              | ([],uu____7091) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   FStar_Errors.raise_error
                     (FStar_Errors.Error_DidNotFail,
                       "This top-level definition was expected to fail, but it succeeded")
                     se.FStar_Syntax_Syntax.sigrng)
              | (uu____7119,FStar_Pervasives_Native.Some (e,n1,n2)) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   (let uu____7142 =
                      let uu____7147 =
                        let uu____7148 = FStar_Util.string_of_int e  in
                        let uu____7149 = FStar_Util.string_of_int n1  in
                        let uu____7150 = FStar_Util.string_of_int n2  in
                        FStar_Util.format3
                          "This top-level definition was expected to raise Error #%s %s times, but it raised it %s times"
                          uu____7148 uu____7149 uu____7150
                         in
                      (FStar_Errors.Error_DidNotFail, uu____7147)  in
                    FStar_Errors.raise_error uu____7142
                      se.FStar_Syntax_Syntax.sigrng))
              | (uu____7159,FStar_Pervasives_Native.None ) -> ([], []))))
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
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7207 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7232 ->
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
            let uu____7287 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1)
               in
            if uu____7287
            then
              let ses1 =
                let uu____7293 =
                  let uu____7294 =
                    let uu____7295 =
                      tc_inductive
                        (let uu___108_7304 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___108_7304.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___108_7304.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___108_7304.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___108_7304.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___108_7304.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___108_7304.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___108_7304.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___108_7304.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___108_7304.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___108_7304.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___108_7304.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___108_7304.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___108_7304.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___108_7304.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___108_7304.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___108_7304.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___108_7304.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___108_7304.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___108_7304.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___108_7304.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___108_7304.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___108_7304.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___108_7304.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___108_7304.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___108_7304.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___108_7304.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___108_7304.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___108_7304.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___108_7304.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___108_7304.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___108_7304.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___108_7304.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___108_7304.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___108_7304.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___108_7304.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___108_7304.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___108_7304.FStar_TypeChecker_Env.dep_graph)
                         }) ses se.FStar_Syntax_Syntax.sigquals lids
                       in
                    FStar_All.pipe_right uu____7295
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____7294
                    (FStar_TypeChecker_Normalize.elim_uvars env1)
                   in
                FStar_All.pipe_right uu____7293
                  FStar_Syntax_Util.ses_of_sigbundle
                 in
              ((let uu____7316 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____7316
                then
                  let uu____7317 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___109_7320 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___109_7320.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___109_7320.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___109_7320.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___109_7320.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Inductive after phase 1: %s\n"
                    uu____7317
                else ());
               ses1)
            else ses  in
          let uu____7327 =
            tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
          (match uu____7327 with
           | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p r; ([se], []))
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
          let uu____7359 = cps_and_elaborate env ne  in
          (match uu____7359 with
           | (ses,ne1,lift_from_pure_opt) ->
               let effect_and_lift_ses =
                 match lift_from_pure_opt with
                 | FStar_Pervasives_Native.Some lift ->
                     [(let uu___110_7396 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___110_7396.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___110_7396.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___110_7396.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___110_7396.FStar_Syntax_Syntax.sigattrs)
                       });
                     lift]
                 | FStar_Pervasives_Native.None  ->
                     [(let uu___111_7398 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___111_7398.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___111_7398.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___111_7398.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___111_7398.FStar_Syntax_Syntax.sigattrs)
                       })]
                  in
               ([], (FStar_List.append ses effect_and_lift_ses)))
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let ne1 =
            let uu____7405 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env)
               in
            if uu____7405
            then
              let ne1 =
                let uu____7407 =
                  let uu____7408 =
                    let uu____7409 =
                      tc_eff_decl
                        (let uu___112_7412 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___112_7412.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___112_7412.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___112_7412.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___112_7412.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___112_7412.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___112_7412.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___112_7412.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___112_7412.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___112_7412.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___112_7412.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___112_7412.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___112_7412.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___112_7412.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___112_7412.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___112_7412.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___112_7412.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___112_7412.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___112_7412.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___112_7412.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___112_7412.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___112_7412.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___112_7412.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___112_7412.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___112_7412.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___112_7412.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___112_7412.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___112_7412.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___112_7412.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___112_7412.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___112_7412.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___112_7412.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___112_7412.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___112_7412.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___112_7412.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___112_7412.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___112_7412.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___112_7412.FStar_TypeChecker_Env.dep_graph)
                         }) ne
                       in
                    FStar_All.pipe_right uu____7409
                      (fun ne1  ->
                         let uu___113_7416 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ne1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___113_7416.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_7416.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_7416.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___113_7416.FStar_Syntax_Syntax.sigattrs)
                         })
                     in
                  FStar_All.pipe_right uu____7408
                    (FStar_TypeChecker_Normalize.elim_uvars env)
                   in
                FStar_All.pipe_right uu____7407
                  FStar_Syntax_Util.eff_decl_of_new_effect
                 in
              ((let uu____7418 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "TwoPhases")
                   in
                if uu____7418
                then
                  let uu____7419 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___114_7422 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___114_7422.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___114_7422.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___114_7422.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___114_7422.FStar_Syntax_Syntax.sigattrs)
                       })
                     in
                  FStar_Util.print1 "Effect decl after phase 1: %s\n"
                    uu____7419
                else ());
               ne1)
            else ne  in
          let ne2 = tc_eff_decl env ne1  in
          let se1 =
            let uu___115_7427 = se  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_new_effect ne2);
              FStar_Syntax_Syntax.sigrng =
                (uu___115_7427.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals =
                (uu___115_7427.FStar_Syntax_Syntax.sigquals);
              FStar_Syntax_Syntax.sigmeta =
                (uu___115_7427.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___115_7427.FStar_Syntax_Syntax.sigattrs)
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
          let uu____7435 =
            let uu____7442 =
              FStar_TypeChecker_Env.lookup_effect_lid env
                sub1.FStar_Syntax_Syntax.source
               in
            monad_signature env sub1.FStar_Syntax_Syntax.source uu____7442
             in
          (match uu____7435 with
           | (a,wp_a_src) ->
               let uu____7457 =
                 let uu____7464 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7464
                  in
               (match uu____7457 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7480 =
                        let uu____7483 =
                          let uu____7484 =
                            let uu____7491 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7491)  in
                          FStar_Syntax_Syntax.NT uu____7484  in
                        [uu____7483]  in
                      FStar_Syntax_Subst.subst uu____7480 wp_b_tgt  in
                    let expected_k =
                      let uu____7499 =
                        let uu____7506 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7511 =
                          let uu____7518 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7518]  in
                        uu____7506 :: uu____7511  in
                      let uu____7535 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7499 uu____7535  in
                    let repr_type eff_name a1 wp =
                      let no_reify l =
                        let uu____7564 =
                          let uu____7569 =
                            FStar_Util.format1 "Effect %s cannot be reified"
                              l.FStar_Ident.str
                             in
                          (FStar_Errors.Fatal_EffectCannotBeReified,
                            uu____7569)
                           in
                        let uu____7570 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error uu____7564 uu____7570  in
                      let uu____7573 =
                        FStar_TypeChecker_Env.effect_decl_opt env eff_name
                         in
                      match uu____7573 with
                      | FStar_Pervasives_Native.None  -> no_reify eff_name
                      | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                          let repr =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [FStar_Syntax_Syntax.U_unknown] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr))
                             in
                          let uu____7607 =
                            let uu____7608 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            Prims.op_Negation uu____7608  in
                          if uu____7607
                          then no_reify eff_name
                          else
                            (let uu____7614 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____7615 =
                               let uu____7622 =
                                 let uu____7623 =
                                   let uu____7638 =
                                     let uu____7647 =
                                       FStar_Syntax_Syntax.as_arg a1  in
                                     let uu____7654 =
                                       let uu____7663 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____7663]  in
                                     uu____7647 :: uu____7654  in
                                   (repr, uu____7638)  in
                                 FStar_Syntax_Syntax.Tm_app uu____7623  in
                               FStar_Syntax_Syntax.mk uu____7622  in
                             uu____7615 FStar_Pervasives_Native.None
                               uu____7614)
                       in
                    let uu____7701 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____7867 =
                            if
                              (FStar_List.length uvs) > (Prims.parse_int "0")
                            then
                              let uu____7876 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____7876 with
                              | (usubst,uvs1) ->
                                  let uu____7899 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____7900 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____7899, uu____7900)
                            else (env, lift_wp)  in
                          (match uu____7867 with
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
                                    let uu____7940 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____7940))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8005 =
                            if
                              (FStar_List.length what) >
                                (Prims.parse_int "0")
                            then
                              let uu____8018 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8018 with
                              | (usubst,uvs) ->
                                  let uu____8043 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8043)
                            else ([], lift)  in
                          (match uu____8005 with
                           | (uvs,lift1) ->
                               ((let uu____8076 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____8076
                                 then
                                   let uu____8077 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____8077
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____8080 =
                                   let uu____8087 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____8087 lift1
                                    in
                                 match uu____8080 with
                                 | (lift2,comp,uu____8110) ->
                                     let uu____8111 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8111 with
                                      | (uu____8138,lift_wp,lift_elab) ->
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
                                            let uu____8164 =
                                              let uu____8167 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8167
                                               in
                                            let uu____8168 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8164, uu____8168)
                                          else
                                            (let uu____8172 =
                                               let uu____8181 =
                                                 let uu____8188 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8188)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8181
                                                in
                                             let uu____8197 =
                                               let uu____8204 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8204)  in
                                             (uu____8172, uu____8197))))))
                       in
                    (match uu____7701 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___116_8264 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___116_8264.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___116_8264.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___116_8264.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___116_8264.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___116_8264.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___116_8264.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___116_8264.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___116_8264.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___116_8264.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___116_8264.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___116_8264.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___116_8264.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___116_8264.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___116_8264.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___116_8264.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___116_8264.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___116_8264.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___116_8264.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___116_8264.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___116_8264.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___116_8264.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___116_8264.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___116_8264.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___116_8264.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___116_8264.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___116_8264.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___116_8264.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___116_8264.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___116_8264.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___116_8264.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___116_8264.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___116_8264.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___116_8264.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___116_8264.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___116_8264.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___116_8264.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___116_8264.FStar_TypeChecker_Env.dep_graph)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8296 =
                                 let uu____8301 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8301 with
                                 | (usubst,uvs1) ->
                                     let uu____8324 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8325 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8324, uu____8325)
                                  in
                               (match uu____8296 with
                                | (env2,lift2) ->
                                    let uu____8330 =
                                      let uu____8337 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8337
                                       in
                                    (match uu____8330 with
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
                                             let uu____8361 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8362 =
                                               let uu____8369 =
                                                 let uu____8370 =
                                                   let uu____8385 =
                                                     let uu____8394 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8401 =
                                                       let uu____8410 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8410]  in
                                                     uu____8394 :: uu____8401
                                                      in
                                                   (lift_wp1, uu____8385)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8370
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8369
                                                in
                                             uu____8362
                                               FStar_Pervasives_Native.None
                                               uu____8361
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8451 =
                                             let uu____8458 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8463 =
                                               let uu____8470 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8475 =
                                                 let uu____8482 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8482]  in
                                               uu____8470 :: uu____8475  in
                                             uu____8458 :: uu____8463  in
                                           let uu____8503 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8451
                                             uu____8503
                                            in
                                         let uu____8506 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8506 with
                                          | (expected_k2,uu____8516,uu____8517)
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
                                                   let uu____8534 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8534))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8544 =
                             let uu____8545 =
                               let uu____8546 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8546
                                 FStar_List.length
                                in
                             uu____8545 <> (Prims.parse_int "1")  in
                           if uu____8544
                           then
                             let uu____8561 =
                               let uu____8566 =
                                 let uu____8567 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8568 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8569 =
                                   let uu____8570 =
                                     let uu____8571 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8571
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8570
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8567 uu____8568 uu____8569
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8566)
                                in
                             FStar_Errors.raise_error uu____8561 r
                           else ());
                          (let uu____8588 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8590 =
                                  let uu____8591 =
                                    let uu____8594 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8594
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8591
                                    FStar_List.length
                                   in
                                uu____8590 <> (Prims.parse_int "1"))
                              in
                           if uu____8588
                           then
                             let uu____8629 =
                               let uu____8634 =
                                 let uu____8635 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8636 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8637 =
                                   let uu____8638 =
                                     let uu____8639 =
                                       let uu____8642 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____8642
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8639
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8638
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8635 uu____8636 uu____8637
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8634)
                                in
                             FStar_Errors.raise_error uu____8629 r
                           else ());
                          (let sub2 =
                             let uu___117_8679 = sub1  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___117_8679.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___117_8679.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp =
                                 (FStar_Pervasives_Native.Some lift_wp);
                               FStar_Syntax_Syntax.lift = lift1
                             }  in
                           let se1 =
                             let uu___118_8681 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___118_8681.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___118_8681.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___118_8681.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___118_8681.FStar_Syntax_Syntax.sigattrs)
                             }  in
                           ([se1], []))))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
          let env0 = env  in
          let uu____8696 =
            if (FStar_List.length uvs) = (Prims.parse_int "0")
            then (env, uvs, tps, c)
            else
              (let uu____8721 = FStar_Syntax_Subst.univ_var_opening uvs  in
               match uu____8721 with
               | (usubst,uvs1) ->
                   let tps1 = FStar_Syntax_Subst.subst_binders usubst tps  in
                   let c1 =
                     let uu____8752 =
                       FStar_Syntax_Subst.shift_subst
                         (FStar_List.length tps1) usubst
                        in
                     FStar_Syntax_Subst.subst_comp uu____8752 c  in
                   let uu____8759 =
                     FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                   (uu____8759, uvs1, tps1, c1))
             in
          (match uu____8696 with
           | (env1,uvs1,tps1,c1) ->
               let env2 = FStar_TypeChecker_Env.set_range env1 r  in
               let uu____8779 = FStar_Syntax_Subst.open_comp tps1 c1  in
               (match uu____8779 with
                | (tps2,c2) ->
                    let uu____8794 =
                      FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                    (match uu____8794 with
                     | (tps3,env3,us) ->
                         let uu____8812 =
                           FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                         (match uu____8812 with
                          | (c3,u,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env3
                                 g;
                               (let tps4 =
                                  FStar_Syntax_Subst.close_binders tps3  in
                                let c4 =
                                  FStar_Syntax_Subst.close_comp tps4 c3  in
                                let uu____8833 =
                                  let uu____8834 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_arrow
                                         (tps4, c4))
                                      FStar_Pervasives_Native.None r
                                     in
                                  FStar_TypeChecker_Util.generalize_universes
                                    env0 uu____8834
                                   in
                                match uu____8833 with
                                | (uvs2,t) ->
                                    let uu____8861 =
                                      let uu____8874 =
                                        let uu____8885 =
                                          let uu____8886 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____8886.FStar_Syntax_Syntax.n
                                           in
                                        (tps4, uu____8885)  in
                                      match uu____8874 with
                                      | ([],FStar_Syntax_Syntax.Tm_arrow
                                         (uu____8907,c5)) -> ([], c5)
                                      | (uu____8947,FStar_Syntax_Syntax.Tm_arrow
                                         (tps5,c5)) -> (tps5, c5)
                                      | uu____8986 ->
                                          failwith
                                            "Impossible (t is an arrow)"
                                       in
                                    (match uu____8861 with
                                     | (tps5,c5) ->
                                         (if
                                            (FStar_List.length uvs2) <>
                                              (Prims.parse_int "1")
                                          then
                                            (let uu____9037 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 uvs2 t
                                                in
                                             match uu____9037 with
                                             | (uu____9042,t1) ->
                                                 let uu____9044 =
                                                   let uu____9049 =
                                                     let uu____9050 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid
                                                        in
                                                     let uu____9051 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs2)
                                                         FStar_Util.string_of_int
                                                        in
                                                     let uu____9052 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t1
                                                        in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       uu____9050 uu____9051
                                                       uu____9052
                                                      in
                                                   (FStar_Errors.Fatal_TooManyUniverse,
                                                     uu____9049)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____9044 r)
                                          else ();
                                          (let se1 =
                                             let uu___119_9055 = se  in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                    (lid, uvs2, tps5, c5,
                                                      flags1));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___119_9055.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___119_9055.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___119_9055.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___119_9055.FStar_Syntax_Syntax.sigattrs)
                                             }  in
                                           ([se1], []))))))))))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____9062,uu____9063,uu____9064) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_9068  ->
                  match uu___88_9068 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____9069 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_let (uu____9074,uu____9075) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_9083  ->
                  match uu___88_9083 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____9084 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          ((let uu____9094 = FStar_TypeChecker_Env.lid_exists env1 lid  in
            if uu____9094
            then
              let uu____9095 =
                let uu____9100 =
                  let uu____9101 = FStar_Ident.text_of_lid lid  in
                  FStar_Util.format1
                    "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                    uu____9101
                   in
                (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                  uu____9100)
                 in
              FStar_Errors.raise_error uu____9095 r
            else ());
           (let uu____9103 =
              if uvs = []
              then
                let uu____9122 =
                  let uu____9123 = FStar_Syntax_Util.type_u ()  in
                  FStar_Pervasives_Native.fst uu____9123  in
                check_and_gen env1 t uu____9122
              else
                (let uu____9129 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                 match uu____9129 with
                 | (uvs1,t1) ->
                     let env2 =
                       FStar_TypeChecker_Env.push_univ_vars env1 uvs1  in
                     let t2 =
                       let uu____9146 =
                         let uu____9147 = FStar_Syntax_Util.type_u ()  in
                         FStar_Pervasives_Native.fst uu____9147  in
                       tc_check_trivial_guard env2 t1 uu____9146  in
                     let t3 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.NoFullNorm;
                         FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                         env2 t2
                        in
                     let uu____9153 =
                       FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                     (uvs1, uu____9153))
               in
            match uu____9103 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___120_9173 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___120_9173.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___120_9173.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___120_9173.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___120_9173.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], [])))
      | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
          let uu____9181 = FStar_Syntax_Subst.open_univ_vars us phi  in
          (match uu____9181 with
           | (us1,phi1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
               let phi2 =
                 let uu____9198 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1)
                    in
                 if uu____9198
                 then
                   let phi2 =
                     let uu____9200 =
                       tc_assume
                         (let uu___121_9203 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___121_9203.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___121_9203.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___121_9203.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___121_9203.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___121_9203.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___121_9203.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___121_9203.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___121_9203.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___121_9203.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___121_9203.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___121_9203.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___121_9203.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___121_9203.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___121_9203.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___121_9203.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___121_9203.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___121_9203.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___121_9203.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___121_9203.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___121_9203.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___121_9203.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___121_9203.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___121_9203.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___121_9203.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___121_9203.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___121_9203.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___121_9203.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___121_9203.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___121_9203.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___121_9203.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___121_9203.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___121_9203.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___121_9203.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___121_9203.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___121_9203.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___121_9203.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___121_9203.FStar_TypeChecker_Env.dep_graph)
                          }) phi1 r
                        in
                     FStar_All.pipe_right uu____9200
                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                          env1)
                      in
                   ((let uu____9205 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____9205
                     then
                       let uu____9206 =
                         FStar_Syntax_Print.term_to_string phi2  in
                       FStar_Util.print1 "Assume after phase 1: %s\n"
                         uu____9206
                     else ());
                    phi2)
                 else phi1  in
               let phi3 = tc_assume env1 phi2 r  in
               let uu____9210 =
                 if us1 = []
                 then FStar_TypeChecker_Util.generalize_universes env1 phi3
                 else
                   (let uu____9230 =
                      FStar_Syntax_Subst.close_univ_vars us1 phi3  in
                    (us1, uu____9230))
                  in
               (match uu____9210 with
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
          let uu____9256 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
          (match uu____9256 with
           | (e1,c,g1) ->
               let uu____9274 =
                 let uu____9281 =
                   let uu____9284 =
                     FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                      in
                   FStar_Pervasives_Native.Some uu____9284  in
                 let uu____9285 =
                   let uu____9290 = FStar_Syntax_Syntax.lcomp_comp c  in
                   (e1, uu____9290)  in
                 FStar_TypeChecker_TcTerm.check_expected_effect env2
                   uu____9281 uu____9285
                  in
               (match uu____9274 with
                | (e2,uu____9300,g) ->
                    ((let uu____9303 = FStar_TypeChecker_Rel.conj_guard g1 g
                         in
                      FStar_TypeChecker_Rel.force_trivial_guard env2
                        uu____9303);
                     (let se1 =
                        let uu___122_9305 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_main e2);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___122_9305.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___122_9305.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___122_9305.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___122_9305.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      ([se1], [])))))
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          ((let uu____9317 = FStar_Options.debug_any ()  in
            if uu____9317
            then
              let uu____9318 =
                FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                 in
              let uu____9319 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.print2 "%s: Found splice of (%s)\n" uu____9318
                uu____9319
            else ());
           (let ses = env.FStar_TypeChecker_Env.splice env t  in
            let lids' =
              FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
            FStar_List.iter
              (fun lid  ->
                 let uu____9332 =
                   FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                 match uu____9332 with
                 | FStar_Pervasives_Native.Some uu____9335 -> ()
                 | FStar_Pervasives_Native.None  ->
                     let uu____9336 =
                       let uu____9341 =
                         let uu____9342 = FStar_Ident.string_of_lid lid  in
                         let uu____9343 =
                           let uu____9344 =
                             FStar_List.map FStar_Ident.string_of_lid lids'
                              in
                           FStar_All.pipe_left (FStar_String.concat ", ")
                             uu____9344
                            in
                         FStar_Util.format2
                           "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                           uu____9342 uu____9343
                          in
                       (FStar_Errors.Fatal_SplicedUndef, uu____9341)  in
                     FStar_Errors.raise_error uu____9336 r) lids;
            ([], ses)))
      | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r  in
          let check_quals_eq l qopt q =
            match qopt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some q
            | FStar_Pervasives_Native.Some q' ->
                let uu____9405 =
                  ((FStar_List.length q) = (FStar_List.length q')) &&
                    (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                       q')
                   in
                if uu____9405
                then FStar_Pervasives_Native.Some q
                else
                  (let uu____9413 =
                     let uu____9418 =
                       let uu____9419 = FStar_Syntax_Print.lid_to_string l
                          in
                       let uu____9420 = FStar_Syntax_Print.quals_to_string q
                          in
                       let uu____9421 = FStar_Syntax_Print.quals_to_string q'
                          in
                       FStar_Util.format3
                         "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                         uu____9419 uu____9420 uu____9421
                        in
                     (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                       uu____9418)
                      in
                   FStar_Errors.raise_error uu____9413 r)
             in
          let rename_parameters lb =
            let rename_in_typ def typ =
              let typ1 = FStar_Syntax_Subst.compress typ  in
              let def_bs =
                let uu____9453 =
                  let uu____9454 = FStar_Syntax_Subst.compress def  in
                  uu____9454.FStar_Syntax_Syntax.n  in
                match uu____9453 with
                | FStar_Syntax_Syntax.Tm_abs (binders,uu____9464,uu____9465)
                    -> binders
                | uu____9486 -> []  in
              match typ1 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                    (val_bs,c);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars = uu____9496;_} ->
                  let has_auto_name bv =
                    FStar_Util.starts_with
                      (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      FStar_Ident.reserved_prefix
                     in
                  let rec rename_binders1 def_bs1 val_bs1 =
                    match (def_bs1, val_bs1) with
                    | ([],uu____9580) -> val_bs1
                    | (uu____9603,[]) -> val_bs1
                    | ((body_bv,uu____9627)::bt,(val_bv,aqual)::vt) ->
                        let uu____9664 = rename_binders1 bt vt  in
                        ((match ((has_auto_name body_bv),
                                  (has_auto_name val_bv))
                          with
                          | (true ,uu____9680) -> (val_bv, aqual)
                          | (false ,true ) ->
                              ((let uu___123_9682 = val_bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (let uu___124_9685 =
                                       val_bv.FStar_Syntax_Syntax.ppname  in
                                     {
                                       FStar_Ident.idText =
                                         ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                       FStar_Ident.idRange =
                                         (uu___124_9685.FStar_Ident.idRange)
                                     });
                                  FStar_Syntax_Syntax.index =
                                    (uu___123_9682.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort =
                                    (uu___123_9682.FStar_Syntax_Syntax.sort)
                                }), aqual)
                          | (false ,false ) -> (val_bv, aqual))) ::
                          uu____9664
                     in
                  let uu____9686 =
                    let uu____9693 =
                      let uu____9694 =
                        let uu____9707 = rename_binders1 def_bs val_bs  in
                        (uu____9707, c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____9694  in
                    FStar_Syntax_Syntax.mk uu____9693  in
                  uu____9686 FStar_Pervasives_Native.None r1
              | uu____9725 -> typ1  in
            let uu___125_9726 = lb  in
            let uu____9727 =
              rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                lb.FStar_Syntax_Syntax.lbtyp
               in
            {
              FStar_Syntax_Syntax.lbname =
                (uu___125_9726.FStar_Syntax_Syntax.lbname);
              FStar_Syntax_Syntax.lbunivs =
                (uu___125_9726.FStar_Syntax_Syntax.lbunivs);
              FStar_Syntax_Syntax.lbtyp = uu____9727;
              FStar_Syntax_Syntax.lbeff =
                (uu___125_9726.FStar_Syntax_Syntax.lbeff);
              FStar_Syntax_Syntax.lbdef =
                (uu___125_9726.FStar_Syntax_Syntax.lbdef);
              FStar_Syntax_Syntax.lbattrs =
                (uu___125_9726.FStar_Syntax_Syntax.lbattrs);
              FStar_Syntax_Syntax.lbpos =
                (uu___125_9726.FStar_Syntax_Syntax.lbpos)
            }  in
          let uu____9730 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.fold_left
                 (fun uu____9781  ->
                    fun lb  ->
                      match uu____9781 with
                      | (gen1,lbs1,quals_opt) ->
                          let lbname =
                            FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                             in
                          let uu____9823 =
                            let uu____9834 =
                              FStar_TypeChecker_Env.try_lookup_val_decl env1
                                (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            match uu____9834 with
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
                                  | uu____9907 ->
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
                                 (let uu____9950 =
                                    FStar_Syntax_Syntax.mk_lb
                                      ((FStar_Util.Inr lbname), uvs,
                                        FStar_Parser_Const.effect_ALL_lid,
                                        tval, def,
                                        (lb.FStar_Syntax_Syntax.lbpos))
                                     in
                                  (false, uu____9950, quals_opt1)))
                             in
                          (match uu____9823 with
                           | (gen2,lb1,quals_opt1) ->
                               (gen2, (lb1 :: lbs1), quals_opt1)))
                 (true, [],
                   (if se.FStar_Syntax_Syntax.sigquals = []
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (se.FStar_Syntax_Syntax.sigquals))))
             in
          (match uu____9730 with
           | (should_generalize,lbs',quals_opt) ->
               let quals =
                 match quals_opt with
                 | FStar_Pervasives_Native.None  ->
                     [FStar_Syntax_Syntax.Visible_default]
                 | FStar_Pervasives_Native.Some q ->
                     let uu____10038 =
                       FStar_All.pipe_right q
                         (FStar_Util.for_some
                            (fun uu___89_10042  ->
                               match uu___89_10042 with
                               | FStar_Syntax_Syntax.Irreducible  -> true
                               | FStar_Syntax_Syntax.Visible_default  -> true
                               | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                               | uu____10043 -> false))
                        in
                     if uu____10038
                     then q
                     else FStar_Syntax_Syntax.Visible_default :: q
                  in
               let lbs'1 = FStar_List.rev lbs'  in
               let e =
                 let uu____10053 =
                   let uu____10060 =
                     let uu____10061 =
                       let uu____10074 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_constant
                              FStar_Const.Const_unit)
                           FStar_Pervasives_Native.None r
                          in
                       (((FStar_Pervasives_Native.fst lbs), lbs'1),
                         uu____10074)
                        in
                     FStar_Syntax_Syntax.Tm_let uu____10061  in
                   FStar_Syntax_Syntax.mk uu____10060  in
                 uu____10053 FStar_Pervasives_Native.None r  in
               let env0 =
                 let uu___126_10093 = env1  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___126_10093.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___126_10093.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___126_10093.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___126_10093.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___126_10093.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___126_10093.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___126_10093.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___126_10093.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___126_10093.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___126_10093.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___126_10093.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___126_10093.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize = should_generalize;
                   FStar_TypeChecker_Env.letrecs =
                     (uu___126_10093.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = true;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___126_10093.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___126_10093.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___126_10093.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___126_10093.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___126_10093.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___126_10093.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___126_10093.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___126_10093.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___126_10093.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___126_10093.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___126_10093.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___126_10093.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___126_10093.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___126_10093.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___126_10093.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___126_10093.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___126_10093.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___126_10093.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___126_10093.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___126_10093.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___126_10093.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___126_10093.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___126_10093.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let e1 =
                 let uu____10095 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env0)
                    in
                 if uu____10095
                 then
                   let drop_lbtyp e_lax =
                     let uu____10102 =
                       let uu____10103 = FStar_Syntax_Subst.compress e_lax
                          in
                       uu____10103.FStar_Syntax_Syntax.n  in
                     match uu____10102 with
                     | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                         let lb_unannotated =
                           let uu____10121 =
                             let uu____10122 = FStar_Syntax_Subst.compress e
                                in
                             uu____10122.FStar_Syntax_Syntax.n  in
                           match uu____10121 with
                           | FStar_Syntax_Syntax.Tm_let
                               ((uu____10125,lb1::[]),uu____10127) ->
                               let uu____10140 =
                                 let uu____10141 =
                                   FStar_Syntax_Subst.compress
                                     lb1.FStar_Syntax_Syntax.lbtyp
                                    in
                                 uu____10141.FStar_Syntax_Syntax.n  in
                               uu____10140 = FStar_Syntax_Syntax.Tm_unknown
                           | uu____10144 ->
                               failwith
                                 "Impossible: first phase lb and second phase lb differ in structure!"
                            in
                         if lb_unannotated
                         then
                           let uu___127_10145 = e_lax  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false,
                                     [(let uu___128_10157 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           FStar_Syntax_Syntax.tun;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbdef);
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___128_10157.FStar_Syntax_Syntax.lbpos)
                                       })]), e2));
                             FStar_Syntax_Syntax.pos =
                               (uu___127_10145.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___127_10145.FStar_Syntax_Syntax.vars)
                           }
                         else e_lax
                     | uu____10159 -> e_lax  in
                   let e1 =
                     let uu____10161 =
                       let uu____10162 =
                         let uu____10163 =
                           FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                             (let uu___129_10172 = env0  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___129_10172.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___129_10172.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___129_10172.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___129_10172.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___129_10172.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___129_10172.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___129_10172.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___129_10172.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___129_10172.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___129_10172.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___129_10172.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___129_10172.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___129_10172.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___129_10172.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___129_10172.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___129_10172.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___129_10172.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___129_10172.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___129_10172.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___129_10172.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___129_10172.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___129_10172.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___129_10172.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___129_10172.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___129_10172.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___129_10172.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___129_10172.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___129_10172.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___129_10172.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___129_10172.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___129_10172.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___129_10172.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___129_10172.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___129_10172.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___129_10172.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___129_10172.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___129_10172.FStar_TypeChecker_Env.dep_graph)
                              }) e
                            in
                         FStar_All.pipe_right uu____10163
                           (fun uu____10183  ->
                              match uu____10183 with
                              | (e1,uu____10191,uu____10192) -> e1)
                          in
                       FStar_All.pipe_right uu____10162
                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                            env0)
                        in
                     FStar_All.pipe_right uu____10161 drop_lbtyp  in
                   ((let uu____10194 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____10194
                     then
                       let uu____10195 = FStar_Syntax_Print.term_to_string e1
                          in
                       FStar_Util.print1 "Let binding after phase 1: %s\n"
                         uu____10195
                     else ());
                    e1)
                 else e  in
               let uu____10198 =
                 let uu____10209 =
                   FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                    in
                 match uu____10209 with
                 | ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                        (lbs1,e2);
                      FStar_Syntax_Syntax.pos = uu____10228;
                      FStar_Syntax_Syntax.vars = uu____10229;_},uu____10230,g)
                     when FStar_TypeChecker_Rel.is_trivial g ->
                     let lbs2 =
                       let uu____10257 =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs1)
                           (FStar_List.map rename_parameters)
                          in
                       ((FStar_Pervasives_Native.fst lbs1), uu____10257)  in
                     let quals1 =
                       match e2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_meta
                           (uu____10275,FStar_Syntax_Syntax.Meta_desugared
                            (FStar_Syntax_Syntax.Masked_effect ))
                           -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                       | uu____10280 -> quals  in
                     ((let uu___130_10288 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___130_10288.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___130_10288.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___130_10288.FStar_Syntax_Syntax.sigattrs)
                       }), lbs2)
                 | uu____10291 ->
                     failwith
                       "impossible (typechecking should preserve Tm_let)"
                  in
               (match uu____10198 with
                | (se1,lbs1) ->
                    (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                       (FStar_List.iter
                          (fun lb  ->
                             let fv =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                                in
                             FStar_TypeChecker_Env.insert_fv_info env1 fv
                               lb.FStar_Syntax_Syntax.lbtyp));
                     (let uu____10340 = log env1  in
                      if uu____10340
                      then
                        let uu____10341 =
                          let uu____10342 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs1)
                              (FStar_List.map
                                 (fun lb  ->
                                    let should_log =
                                      let uu____10357 =
                                        let uu____10366 =
                                          let uu____10367 =
                                            let uu____10370 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            uu____10370.FStar_Syntax_Syntax.fv_name
                                             in
                                          uu____10367.FStar_Syntax_Syntax.v
                                           in
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env1 uu____10366
                                         in
                                      match uu____10357 with
                                      | FStar_Pervasives_Native.None  -> true
                                      | uu____10377 -> false  in
                                    if should_log
                                    then
                                      let uu____10386 =
                                        FStar_Syntax_Print.lbname_to_string
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      let uu____10387 =
                                        FStar_Syntax_Print.term_to_string
                                          lb.FStar_Syntax_Syntax.lbtyp
                                         in
                                      FStar_Util.format2 "let %s : %s"
                                        uu____10386 uu____10387
                                    else ""))
                             in
                          FStar_All.pipe_right uu____10342
                            (FStar_String.concat "\n")
                           in
                        FStar_Util.print1 "%s\n" uu____10341
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
             (fun uu___90_10439  ->
                match uu___90_10439 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____10440 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____10448) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____10454 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____10463 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____10468 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____10483 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____10508 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10532) ->
          let uu____10541 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10541
          then
            let for_export_bundle se1 uu____10576 =
              match uu____10576 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____10615,uu____10616) ->
                       let dec =
                         let uu___131_10626 = se1  in
                         let uu____10627 =
                           let uu____10628 =
                             let uu____10635 =
                               let uu____10636 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____10636  in
                             (l, us, uu____10635)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____10628
                            in
                         {
                           FStar_Syntax_Syntax.sigel = uu____10627;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___131_10626.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___131_10626.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___131_10626.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____10646,uu____10647,uu____10648) ->
                       let dec =
                         let uu___132_10654 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_10654.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_10654.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_10654.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____10659 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____10681,uu____10682,uu____10683)
          ->
          let uu____10684 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10684 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____10705 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____10705
          then
            ([(let uu___133_10721 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___133_10721.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___133_10721.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___133_10721.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____10723 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___91_10727  ->
                       match uu___91_10727 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____10728 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____10733 ->
                           true
                       | uu____10734 -> false))
                in
             if uu____10723 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____10752 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____10757 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10762 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10767 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10772 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10790) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10801 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____10801
          then ([], hidden)
          else
            (let dec =
               let uu____10818 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____10818;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____10829 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____10829
          then
            let uu____10838 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___134_10851 = se  in
                      let uu____10852 =
                        let uu____10853 =
                          let uu____10860 =
                            let uu____10861 =
                              let uu____10864 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____10864.FStar_Syntax_Syntax.fv_name  in
                            uu____10861.FStar_Syntax_Syntax.v  in
                          (uu____10860, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____10853  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____10852;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___134_10851.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___134_10851.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___134_10851.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____10838, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____10884 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____10901 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____10916) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____10919 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10920 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____10930 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____10930) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____10931,uu____10932,uu____10933) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___92_10937  ->
                  match uu___92_10937 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10938 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____10939,uu____10940) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___92_10948  ->
                  match uu___92_10948 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10949 -> false))
          -> env
      | uu____10950 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____11018 se =
        match uu____11018 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____11071 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____11071
              then
                let uu____11072 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____11072
              else ());
             (let uu____11074 = tc_decl env1 se  in
              match uu____11074 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____11124 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____11124
                             then
                               let uu____11125 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____11125
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
                    (let uu____11148 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____11148
                     then
                       let uu____11149 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____11155 =
                                  let uu____11156 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____11156 "\n"  in
                                Prims.strcat s uu____11155) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____11149
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____11161 =
                       let uu____11170 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____11170
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____11209 se1 =
                            match uu____11209 with
                            | (exports1,hidden1) ->
                                let uu____11237 = for_export hidden1 se1  in
                                (match uu____11237 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____11161 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___135_11316 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___135_11316.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___135_11316.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___135_11316.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___135_11316.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____11398 = acc  in
        match uu____11398 with
        | (uu____11433,uu____11434,env1,uu____11436) ->
            let uu____11449 =
              FStar_Util.record_time
                (fun uu____11495  -> process_one_decl acc se)
               in
            (match uu____11449 with
             | (r,ms_elapsed) ->
                 ((let uu____11559 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____11559
                   then
                     let uu____11560 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____11561 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____11560 uu____11561
                   else ());
                  r))
         in
      let uu____11563 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____11563 with
      | (ses1,exports,env1,uu____11611) ->
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
          let uu___136_11648 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___136_11648.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___136_11648.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___136_11648.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___136_11648.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___136_11648.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___136_11648.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___136_11648.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___136_11648.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___136_11648.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___136_11648.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___136_11648.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___136_11648.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___136_11648.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___136_11648.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___136_11648.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___136_11648.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___136_11648.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___136_11648.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___136_11648.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___136_11648.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___136_11648.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___136_11648.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___136_11648.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___136_11648.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___136_11648.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___136_11648.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___136_11648.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___136_11648.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___136_11648.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___136_11648.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___136_11648.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___136_11648.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___136_11648.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___136_11648.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___136_11648.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____11665 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____11665 with
          | (univs2,t1) ->
              ((let uu____11673 =
                  let uu____11674 =
                    let uu____11679 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____11679  in
                  FStar_All.pipe_left uu____11674
                    (FStar_Options.Other "Exports")
                   in
                if uu____11673
                then
                  let uu____11680 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____11681 =
                    let uu____11682 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____11682
                      (FStar_String.concat ", ")
                     in
                  let uu____11693 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____11680 uu____11681 uu____11693
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____11696 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____11696 (fun a239  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____11722 =
             let uu____11723 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____11724 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____11723 uu____11724
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____11722);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11733) ->
              let uu____11742 =
                let uu____11743 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11743  in
              if uu____11742
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____11753,uu____11754) ->
              let t =
                let uu____11766 =
                  let uu____11773 =
                    let uu____11774 =
                      let uu____11787 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____11787)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____11774  in
                  FStar_Syntax_Syntax.mk uu____11773  in
                uu____11766 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____11804,uu____11805,uu____11806) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____11814 =
                let uu____11815 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11815  in
              if uu____11814 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____11819,lbs),uu____11821) ->
              let uu____11830 =
                let uu____11831 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11831  in
              if uu____11830
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
              let uu____11850 =
                let uu____11851 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____11851  in
              if uu____11850
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____11866 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____11867 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11874 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11875 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____11876 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____11877 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____11884 -> ()  in
        let uu____11885 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____11885 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____11980) -> true
             | uu____11981 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____12008 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____12039 ->
                   let uu____12040 =
                     let uu____12047 =
                       let uu____12048 =
                         let uu____12061 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____12061)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____12048  in
                     FStar_Syntax_Syntax.mk uu____12047  in
                   uu____12040 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____12079,uu____12080) ->
            let s1 =
              let uu___137_12090 = s  in
              let uu____12091 =
                let uu____12092 =
                  let uu____12099 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____12099)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____12092  in
              let uu____12100 =
                let uu____12103 =
                  let uu____12106 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____12106  in
                FStar_Syntax_Syntax.Assumption :: uu____12103  in
              {
                FStar_Syntax_Syntax.sigel = uu____12091;
                FStar_Syntax_Syntax.sigrng =
                  (uu___137_12090.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____12100;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___137_12090.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___137_12090.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____12109 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____12133 lbdef =
        match uu____12133 with
        | (uvs,t) ->
            let attrs =
              let uu____12144 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____12144
              then
                let uu____12147 =
                  let uu____12148 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____12148
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____12147 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___138_12150 = s  in
            let uu____12151 =
              let uu____12154 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____12154  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___138_12150.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____12151;
              FStar_Syntax_Syntax.sigmeta =
                (uu___138_12150.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____12170 -> failwith "Impossible!"  in
        let c_opt =
          let uu____12176 = FStar_Syntax_Util.is_unit t  in
          if uu____12176
          then
            let uu____12181 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____12181
          else
            (let uu____12187 =
               let uu____12188 = FStar_Syntax_Subst.compress t  in
               uu____12188.FStar_Syntax_Syntax.n  in
             match uu____12187 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____12195,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____12215 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____12238 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____12238
           then
             let uu____12239 =
               let uu____12240 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____12240 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____12239
           else
             (let uu____12246 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____12246))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____12257 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____12276 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____12293 ->
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
                            (lid,uu____12337,uu____12338,uu____12339,uu____12340,uu____12341)
                            ->
                            ((let uu____12351 =
                                let uu____12354 =
                                  FStar_ST.op_Bang abstract_inductive_tycons
                                   in
                                lid :: uu____12354  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_tycons uu____12351);
                             (let uu____12455 = vals_of_abstract_inductive s1
                                 in
                              FStar_List.append uu____12455 sigelts1))
                        | FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____12459,uu____12460,uu____12461,uu____12462,uu____12463)
                            ->
                            ((let uu____12469 =
                                let uu____12472 =
                                  FStar_ST.op_Bang
                                    abstract_inductive_datacons
                                   in
                                lid :: uu____12472  in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_datacons uu____12469);
                             sigelts1)
                        | uu____12573 ->
                            failwith
                              "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                   [])
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____12580 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____12580
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____12586 =
                   let uu___139_12587 = s  in
                   let uu____12588 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___139_12587.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___139_12587.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____12588;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___139_12587.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___139_12587.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____12586])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____12598 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____12598
            then []
            else
              (let uu____12602 = lbs  in
               match uu____12602 with
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
                       (fun uu____12661  ->
                          match uu____12661 with
                          | (uu____12668,t,uu____12670) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs_and_defs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____12686  ->
                            match uu____12686 with
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
                          (fun uu____12710  ->
                             match uu____12710 with
                             | (uu____12717,t,uu____12719) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs_and_defs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____12727,uu____12728) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____12733 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____12788 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                        in
                     FStar_Ident.lid_equals lid uu____12788) uu____12733
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____12791 =
                   let uu___140_12792 = s  in
                   let uu____12793 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___140_12792.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___140_12792.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____12793;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___140_12792.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___140_12792.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____12791]
               else [])
            else
              (let uu____12798 =
                 let uu___141_12799 = s  in
                 let uu____12800 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___141_12799.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___141_12799.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____12800;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___141_12799.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___141_12799.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____12798])
        | FStar_Syntax_Syntax.Sig_new_effect uu____12803 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12804 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____12805 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12806 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____12819 -> [s]  in
      let uu___142_12820 = m  in
      let uu____12821 =
        let uu____12822 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____12822 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___142_12820.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____12821;
        FStar_Syntax_Syntax.exports =
          (uu___142_12820.FStar_Syntax_Syntax.exports);
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
        (fun uu____12866  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____12905  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____12918 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____12918
  
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
      (let uu____12981 = FStar_Options.debug_any ()  in
       if uu____12981
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
         let uu___143_12986 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___143_12986.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___143_12986.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___143_12986.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___143_12986.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___143_12986.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___143_12986.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___143_12986.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___143_12986.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___143_12986.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___143_12986.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___143_12986.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___143_12986.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___143_12986.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___143_12986.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___143_12986.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___143_12986.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___143_12986.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___143_12986.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___143_12986.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___143_12986.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___143_12986.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___143_12986.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___143_12986.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___143_12986.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___143_12986.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___143_12986.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___143_12986.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___143_12986.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___143_12986.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___143_12986.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___143_12986.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___143_12986.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___143_12986.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___143_12986.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___143_12986.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___143_12986.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____12988 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____12988 with
       | (ses,exports,env3) ->
           ((let uu___144_13021 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___144_13021.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___144_13021.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___144_13021.FStar_Syntax_Syntax.is_interface)
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
        let uu____13049 = tc_decls env decls  in
        match uu____13049 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___145_13080 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___145_13080.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___145_13080.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___145_13080.FStar_Syntax_Syntax.is_interface)
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
        let uu____13146 = tc_partial_modul env01 m  in
        match uu____13146 with
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
              (((Prims.op_Negation loading_from_cache) &&
                  (Prims.op_Negation iface_exists))
                 && (FStar_Options.use_extracted_interfaces ()))
                && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____13196 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____13196
                then
                  let uu____13197 =
                    let uu____13198 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13198 then "" else " (in lax mode) "  in
                  let uu____13200 =
                    let uu____13201 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13201
                    then
                      let uu____13202 =
                        let uu____13203 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____13203 "\n"  in
                      Prims.strcat "\nfrom: " uu____13202
                    else ""  in
                  let uu____13205 =
                    let uu____13206 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____13206
                    then
                      let uu____13207 =
                        let uu____13208 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____13208 "\n"  in
                      Prims.strcat "\nto: " uu____13207
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____13197
                    uu____13200 uu____13205
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___146_13214 = en0  in
                    let uu____13215 =
                      let uu____13228 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____13228, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___146_13214.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___146_13214.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___146_13214.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___146_13214.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___146_13214.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___146_13214.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___146_13214.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___146_13214.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___146_13214.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___146_13214.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___146_13214.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___146_13214.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___146_13214.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___146_13214.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___146_13214.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___146_13214.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___146_13214.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___146_13214.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___146_13214.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___146_13214.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___146_13214.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___146_13214.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___146_13214.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___146_13214.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___146_13214.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___146_13214.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___146_13214.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___146_13214.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____13215;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___146_13214.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___146_13214.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___146_13214.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___146_13214.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___146_13214.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___146_13214.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___146_13214.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___146_13214.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___146_13214.FStar_TypeChecker_Env.dep_graph)
                    }  in
                  let uu____13265 =
                    let uu____13266 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____13266  in
                  if uu____13265
                  then
                    ((let uu____13268 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____13268 (fun a240  -> ()));
                     z3_reset_options en01)
                  else en01  in
                let uu____13270 = tc_modul en0 modul_iface true  in
                match uu____13270 with
                | (modul_iface1,must_be_none,env) ->
                    if must_be_none <> FStar_Pervasives_Native.None
                    then
                      failwith
                        "Impossible! finish_partial_module: expected the second component to be None"
                    else
                      (((let uu___147_13316 = m  in
                         {
                           FStar_Syntax_Syntax.name =
                             (uu___147_13316.FStar_Syntax_Syntax.name);
                           FStar_Syntax_Syntax.declarations =
                             (uu___147_13316.FStar_Syntax_Syntax.declarations);
                           FStar_Syntax_Syntax.exports =
                             (modul_iface1.FStar_Syntax_Syntax.exports);
                           FStar_Syntax_Syntax.is_interface =
                             (uu___147_13316.FStar_Syntax_Syntax.is_interface)
                         })), (FStar_Pervasives_Native.Some modul_iface1),
                        env)))
            else
              (let modul =
                 let uu____13319 = FStar_Options.use_extracted_interfaces ()
                    in
                 if uu____13319
                 then
                   let uu___148_13320 = m  in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___148_13320.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations =
                       (uu___148_13320.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.exports =
                       (m.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___148_13320.FStar_Syntax_Syntax.is_interface)
                   }
                 else
                   (let uu___149_13322 = m  in
                    {
                      FStar_Syntax_Syntax.name =
                        (uu___149_13322.FStar_Syntax_Syntax.name);
                      FStar_Syntax_Syntax.declarations =
                        (uu___149_13322.FStar_Syntax_Syntax.declarations);
                      FStar_Syntax_Syntax.exports = exports;
                      FStar_Syntax_Syntax.is_interface =
                        (uu___149_13322.FStar_Syntax_Syntax.is_interface)
                    })
                  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____13325 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____13325 FStar_Util.smap_clear);
               (let uu____13353 =
                  ((let uu____13356 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____13356) &&
                     (let uu____13358 =
                        FStar_Options.use_extracted_interfaces ()  in
                      Prims.op_Negation uu____13358))
                    && (Prims.op_Negation loading_from_cache)
                   in
                if uu____13353 then check_exports env modul exports else ());
               (let uu____13361 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____13361 (fun a241  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____13365 =
                  let uu____13366 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____13366  in
                if uu____13365
                then
                  let uu____13367 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____13367 (fun a242  -> ())
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
        let uu____13383 =
          let uu____13384 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____13384  in
        push_context env uu____13383  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____13403 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____13414 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____13414 with | (uu____13423,uu____13424,env3) -> env3
  
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
        (let uu____13454 = FStar_Options.debug_any ()  in
         if uu____13454
         then
           let uu____13455 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____13455
         else ());
        (let env1 =
           let uu___150_13459 = env  in
           let uu____13460 =
             let uu____13461 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____13461  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___150_13459.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___150_13459.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___150_13459.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___150_13459.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___150_13459.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___150_13459.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___150_13459.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___150_13459.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___150_13459.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___150_13459.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___150_13459.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___150_13459.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___150_13459.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___150_13459.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___150_13459.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___150_13459.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___150_13459.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___150_13459.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___150_13459.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____13460;
             FStar_TypeChecker_Env.lax_universes =
               (uu___150_13459.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___150_13459.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___150_13459.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___150_13459.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___150_13459.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___150_13459.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___150_13459.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___150_13459.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___150_13459.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___150_13459.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.proof_ns =
               (uu___150_13459.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___150_13459.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___150_13459.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___150_13459.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___150_13459.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___150_13459.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___150_13459.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___150_13459.FStar_TypeChecker_Env.dep_graph)
           }  in
         let uu____13462 = tc_modul env1 m b  in
         match uu____13462 with
         | (m1,m_iface_opt,env2) ->
             ((let uu____13487 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____13487
               then
                 let uu____13488 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____13488
               else ());
              (let uu____13491 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____13491
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
                         let uu____13524 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____13524 with
                         | (univnames1,e) ->
                             let uu___151_13531 = lb  in
                             let uu____13532 =
                               let uu____13535 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____13535 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13532;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___151_13531.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___152_13536 = se  in
                       let uu____13537 =
                         let uu____13538 =
                           let uu____13545 =
                             let uu____13546 = FStar_List.map update lbs  in
                             (b1, uu____13546)  in
                           (uu____13545, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____13538  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____13537;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13536.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13536.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13536.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___152_13536.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____13553 -> se  in
                 let normalized_module =
                   let uu___153_13555 = m1  in
                   let uu____13556 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___153_13555.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____13556;
                     FStar_Syntax_Syntax.exports =
                       (uu___153_13555.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___153_13555.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____13557 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____13557
               else ());
              (m1, m_iface_opt, env2)))
  