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
          let uu___364_54 = env  in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid  in (lid, uu____80)  in
              FStar_Pervasives_Native.Some uu____75  in
            (tbl, uu____68)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___364_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___364_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___364_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___364_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___364_54.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___364_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___364_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___364_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___364_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___364_54.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___364_54.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___364_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___364_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___364_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___364_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___364_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___364_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___364_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___364_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___364_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___364_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___364_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___364_54.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___364_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___364_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___364_54.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___364_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___364_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___364_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___364_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___364_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___364_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___364_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___364_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___364_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___364_54.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___364_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___364_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___364_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___364_54.FStar_TypeChecker_Env.dep_graph)
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
          let uu___365_104 = env  in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid  in (lid, uu____130)
                 in
              FStar_Pervasives_Native.Some uu____125  in
            (tbl, uu____118)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___365_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___365_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___365_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___365_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___365_104.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___365_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___365_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___365_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___365_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___365_104.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___365_104.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___365_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___365_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___365_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___365_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___365_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___365_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___365_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___365_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___365_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___365_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___365_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___365_104.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___365_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___365_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___365_104.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___365_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___365_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___365_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___365_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___365_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___365_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___365_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___365_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___365_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___365_104.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___365_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___365_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___365_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___365_104.FStar_TypeChecker_Env.dep_graph)
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
             | (a,uu____342)::(wp,uu____344)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____373 -> fail1 ())
        | uu____374 -> fail1 ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____385 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____385 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____415 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____415 t  in
          let open_univs_binders n_binders bs =
            let uu____429 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____429 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____439 =
            let uu____446 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____447 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____446 uu____447  in
          (match uu____439 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____458 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____458 with
                | (effect_params,env1,uu____467) ->
                    let uu____468 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____468 with
                     | (signature,uu____474) ->
                         let ed1 =
                           let uu___366_476 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___366_476.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___366_476.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___366_476.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___366_476.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___366_476.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___366_476.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___366_476.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___366_476.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___366_476.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___366_476.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___366_476.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___366_476.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___366_476.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___366_476.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___366_476.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___366_476.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___366_476.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___366_476.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____504 ->
                               let op uu____536 =
                                 match uu____536 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____556 =
                                       let uu____557 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____566 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____557
                                         uu____566
                                        in
                                     (us, uu____556)
                                  in
                               let uu___367_575 = ed1  in
                               let uu____576 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____577 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____578 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____579 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____580 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____581 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____582 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____583 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____584 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____585 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____586 =
                                 let uu____587 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____587  in
                               let uu____598 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____599 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____600 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___368_608 = a  in
                                      let uu____609 =
                                        let uu____610 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____610
                                         in
                                      let uu____621 =
                                        let uu____622 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____622
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___368_608.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___368_608.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___368_608.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___368_608.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____609;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____621
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___367_575.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___367_575.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___367_575.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___367_575.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____576;
                                 FStar_Syntax_Syntax.bind_wp = uu____577;
                                 FStar_Syntax_Syntax.if_then_else = uu____578;
                                 FStar_Syntax_Syntax.ite_wp = uu____579;
                                 FStar_Syntax_Syntax.stronger = uu____580;
                                 FStar_Syntax_Syntax.close_wp = uu____581;
                                 FStar_Syntax_Syntax.assert_p = uu____582;
                                 FStar_Syntax_Syntax.assume_p = uu____583;
                                 FStar_Syntax_Syntax.null_wp = uu____584;
                                 FStar_Syntax_Syntax.trivial = uu____585;
                                 FStar_Syntax_Syntax.repr = uu____586;
                                 FStar_Syntax_Syntax.return_repr = uu____598;
                                 FStar_Syntax_Syntax.bind_repr = uu____599;
                                 FStar_Syntax_Syntax.actions = uu____600;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___367_575.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____667 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____672 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____667 uu____672  in
                           let uu____679 =
                             let uu____680 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____680.FStar_Syntax_Syntax.n  in
                           match uu____679 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____719)::(wp,uu____721)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____750 -> fail1 signature1)
                           | uu____751 -> fail1 signature1  in
                         let uu____752 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____752 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____776 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____783 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____783 with
                                     | (signature1,uu____795) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____796 ->
                                    let uu____799 =
                                      let uu____804 =
                                        let uu____805 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____805)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____804
                                       in
                                    (match uu____799 with
                                     | (uu____818,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____821 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____821
                                 in
                              ((let uu____823 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____823
                                then
                                  let uu____824 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____825 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____826 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____827 =
                                    let uu____828 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____828
                                     in
                                  let uu____829 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____824 uu____825 uu____826 uu____827
                                    uu____829
                                else ());
                               (let check_and_gen' env3 uu____861 k =
                                  match uu____861 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____897::uu____898 ->
                                           let uu____901 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____901 with
                                            | (us1,t1) ->
                                                let uu____924 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____924 with
                                                 | (us2,t2) ->
                                                     let uu____939 =
                                                       let uu____940 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____940 t2 k
                                                        in
                                                     let uu____941 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____941))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____960 =
                                      let uu____969 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____976 =
                                        let uu____985 =
                                          let uu____992 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____992
                                           in
                                        [uu____985]  in
                                      uu____969 :: uu____976  in
                                    let uu____1011 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____960
                                      uu____1011
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____1015 = fresh_effect_signature ()
                                     in
                                  match uu____1015 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____1031 =
                                          let uu____1040 =
                                            let uu____1047 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1047
                                             in
                                          [uu____1040]  in
                                        let uu____1060 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1031
                                          uu____1060
                                         in
                                      let expected_k =
                                        let uu____1066 =
                                          let uu____1075 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____1082 =
                                            let uu____1091 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1098 =
                                              let uu____1107 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____1114 =
                                                let uu____1123 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____1130 =
                                                  let uu____1139 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____1139]  in
                                                uu____1123 :: uu____1130  in
                                              uu____1107 :: uu____1114  in
                                            uu____1091 :: uu____1098  in
                                          uu____1075 :: uu____1082  in
                                        let uu____1182 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____1066
                                          uu____1182
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____1195 =
                                      let uu____1198 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1198
                                       in
                                    let uu____1199 =
                                      let uu____1200 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1200
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1195
                                      uu____1199
                                     in
                                  let expected_k =
                                    let uu____1212 =
                                      let uu____1221 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1228 =
                                        let uu____1237 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____1244 =
                                          let uu____1253 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____1260 =
                                            let uu____1269 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1269]  in
                                          uu____1253 :: uu____1260  in
                                        uu____1237 :: uu____1244  in
                                      uu____1221 :: uu____1228  in
                                    let uu____1306 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1212
                                      uu____1306
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1321 =
                                      let uu____1330 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1337 =
                                        let uu____1346 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____1346]  in
                                      uu____1330 :: uu____1337  in
                                    let uu____1371 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1321
                                      uu____1371
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____1375 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1375 with
                                  | (t,uu____1381) ->
                                      let expected_k =
                                        let uu____1385 =
                                          let uu____1394 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1401 =
                                            let uu____1410 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____1417 =
                                              let uu____1426 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____1426]  in
                                            uu____1410 :: uu____1417  in
                                          uu____1394 :: uu____1401  in
                                        let uu____1457 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____1385
                                          uu____1457
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____1470 =
                                      let uu____1473 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      FStar_Pervasives_Native.Some uu____1473
                                       in
                                    let uu____1474 =
                                      let uu____1475 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____1475
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv uu____1470
                                      uu____1474
                                     in
                                  let b_wp_a =
                                    let uu____1487 =
                                      let uu____1496 =
                                        let uu____1503 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1503
                                         in
                                      [uu____1496]  in
                                    let uu____1516 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1487
                                      uu____1516
                                     in
                                  let expected_k =
                                    let uu____1522 =
                                      let uu____1531 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1538 =
                                        let uu____1547 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1554 =
                                          let uu____1563 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1563]  in
                                        uu____1547 :: uu____1554  in
                                      uu____1531 :: uu____1538  in
                                    let uu____1594 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1522
                                      uu____1594
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1609 =
                                      let uu____1618 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1625 =
                                        let uu____1634 =
                                          let uu____1641 =
                                            let uu____1642 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1642
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1641
                                           in
                                        let uu____1651 =
                                          let uu____1660 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1660]  in
                                        uu____1634 :: uu____1651  in
                                      uu____1618 :: uu____1625  in
                                    let uu____1691 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1609
                                      uu____1691
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1706 =
                                      let uu____1715 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1722 =
                                        let uu____1731 =
                                          let uu____1738 =
                                            let uu____1739 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1739
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1738
                                           in
                                        let uu____1748 =
                                          let uu____1757 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1757]  in
                                        uu____1731 :: uu____1748  in
                                      uu____1715 :: uu____1722  in
                                    let uu____1788 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1706
                                      uu____1788
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1803 =
                                      let uu____1812 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1812]  in
                                    let uu____1831 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1803
                                      uu____1831
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1835 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1835 with
                                  | (t,uu____1841) ->
                                      let expected_k =
                                        let uu____1845 =
                                          let uu____1854 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1861 =
                                            let uu____1870 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1870]  in
                                          uu____1854 :: uu____1861  in
                                        let uu____1895 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1845
                                          uu____1895
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1898 =
                                  let uu____1911 =
                                    let uu____1912 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1912.FStar_Syntax_Syntax.n  in
                                  match uu____1911 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1931 ->
                                      let repr =
                                        let uu____1933 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1933 with
                                        | (t,uu____1939) ->
                                            let expected_k =
                                              let uu____1943 =
                                                let uu____1952 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1959 =
                                                  let uu____1968 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1968]  in
                                                uu____1952 :: uu____1959  in
                                              let uu____1993 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1943 uu____1993
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
                                        let uu____2010 =
                                          let uu____2017 =
                                            let uu____2018 =
                                              let uu____2035 =
                                                let uu____2046 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____2055 =
                                                  let uu____2066 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____2066]  in
                                                uu____2046 :: uu____2055  in
                                              (repr1, uu____2035)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____2018
                                             in
                                          FStar_Syntax_Syntax.mk uu____2017
                                           in
                                        uu____2010
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____2127 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____2127 wp  in
                                      let destruct_repr t =
                                        let uu____2142 =
                                          let uu____2143 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____2143.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2142 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____2154,(t1,uu____2156)::
                                             (wp,uu____2158)::[])
                                            -> (t1, wp)
                                        | uu____2217 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____2228 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____2228
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____2229 =
                                          fresh_effect_signature ()  in
                                        match uu____2229 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____2245 =
                                                let uu____2254 =
                                                  let uu____2261 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____2261
                                                   in
                                                [uu____2254]  in
                                              let uu____2274 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2245 uu____2274
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
                                              let uu____2280 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____2280
                                               in
                                            let wp_g_x =
                                              let uu____2284 =
                                                let uu____2289 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____2290 =
                                                  let uu____2291 =
                                                    let uu____2300 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2300
                                                     in
                                                  [uu____2291]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____2289 uu____2290
                                                 in
                                              uu____2284
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____2333 =
                                                  let uu____2338 =
                                                    let uu____2339 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2339
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____2348 =
                                                    let uu____2349 =
                                                      let uu____2352 =
                                                        let uu____2355 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____2356 =
                                                          let uu____2359 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____2360 =
                                                            let uu____2363 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____2364 =
                                                              let uu____2367
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____2367]
                                                               in
                                                            uu____2363 ::
                                                              uu____2364
                                                             in
                                                          uu____2359 ::
                                                            uu____2360
                                                           in
                                                        uu____2355 ::
                                                          uu____2356
                                                         in
                                                      r :: uu____2352  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____2349
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____2338 uu____2348
                                                   in
                                                uu____2333
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let maybe_range_arg =
                                              let uu____2387 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs
                                                 in
                                              if uu____2387
                                              then
                                                let uu____2396 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range
                                                   in
                                                let uu____2403 =
                                                  let uu____2412 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  [uu____2412]  in
                                                uu____2396 :: uu____2403
                                              else []  in
                                            let expected_k =
                                              let uu____2447 =
                                                let uu____2456 =
                                                  let uu____2465 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____2472 =
                                                    let uu____2481 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b
                                                       in
                                                    [uu____2481]  in
                                                  uu____2465 :: uu____2472
                                                   in
                                                let uu____2506 =
                                                  let uu____2515 =
                                                    let uu____2524 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____2531 =
                                                      let uu____2540 =
                                                        let uu____2547 =
                                                          let uu____2548 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____2548
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____2547
                                                         in
                                                      let uu____2549 =
                                                        let uu____2558 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____2565 =
                                                          let uu____2574 =
                                                            let uu____2581 =
                                                              let uu____2582
                                                                =
                                                                let uu____2591
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____2591]
                                                                 in
                                                              let uu____2610
                                                                =
                                                                let uu____2613
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____2613
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____2582
                                                                uu____2610
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____2581
                                                             in
                                                          [uu____2574]  in
                                                        uu____2558 ::
                                                          uu____2565
                                                         in
                                                      uu____2540 ::
                                                        uu____2549
                                                       in
                                                    uu____2524 :: uu____2531
                                                     in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____2515
                                                   in
                                                FStar_List.append uu____2456
                                                  uu____2506
                                                 in
                                              let uu____2658 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____2447 uu____2658
                                               in
                                            let uu____2661 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            (match uu____2661 with
                                             | (expected_k1,uu____2669,uu____2670)
                                                 ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env4 =
                                                   let uu___369_2677 = env3
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_sig
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.gamma_sig);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.attrtab
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.attrtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.phase1
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.phase1);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.uvar_subtyping
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.uvar_subtyping);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___369_2677.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____2689 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____2689
                                           in
                                        let res =
                                          let wp =
                                            let uu____2696 =
                                              let uu____2701 =
                                                let uu____2702 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2702
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____2711 =
                                                let uu____2712 =
                                                  let uu____2715 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____2716 =
                                                    let uu____2719 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____2719]  in
                                                  uu____2715 :: uu____2716
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____2712
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____2701 uu____2711
                                               in
                                            uu____2696
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____2733 =
                                            let uu____2742 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____2749 =
                                              let uu____2758 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____2758]  in
                                            uu____2742 :: uu____2749  in
                                          let uu____2783 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____2733
                                            uu____2783
                                           in
                                        let uu____2786 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k
                                           in
                                        match uu____2786 with
                                        | (expected_k1,uu____2794,uu____2795)
                                            ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____2801 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____2801 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____2824 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____2837 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____2849 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____2849 with
                                               | (usubst,uvs) ->
                                                   let uu____2872 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs
                                                      in
                                                   let uu____2873 =
                                                     let uu___370_2874 = act
                                                        in
                                                     let uu____2875 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params
                                                        in
                                                     let uu____2876 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____2877 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___370_2874.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___370_2874.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____2875;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____2876;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____2877
                                                     }  in
                                                   (uu____2872, uu____2873))
                                             in
                                          match uu____2837 with
                                          | (env3,act1) ->
                                              let act_typ =
                                                let uu____2881 =
                                                  let uu____2882 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____2882.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____2881 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____2908 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____2908
                                                    then
                                                      let uu____2909 =
                                                        let uu____2912 =
                                                          let uu____2913 =
                                                            let uu____2914 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2914
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____2913
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____2912
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____2909
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____2936 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____2937 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ
                                                 in
                                              (match uu____2937 with
                                               | (act_typ1,uu____2945,g_t) ->
                                                   let env' =
                                                     let uu___371_2948 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___371_2948.FStar_TypeChecker_Env.dep_graph)
                                                     }  in
                                                   ((let uu____2950 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____2950
                                                     then
                                                       let uu____2951 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____2952 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____2953 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____2951
                                                         uu____2952
                                                         uu____2953
                                                     else ());
                                                    (let uu____2955 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____2955 with
                                                     | (act_defn,uu____2963,g_a)
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
                                                         let uu____2967 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs,c) ->
                                                               let uu____3003
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c
                                                                  in
                                                               (match uu____3003
                                                                with
                                                                | (bs1,uu____3015)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____3022
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3022
                                                                     in
                                                                    let uu____3025
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____3025
                                                                    with
                                                                    | 
                                                                    (k1,uu____3039,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____3043 ->
                                                               let uu____3044
                                                                 =
                                                                 let uu____3049
                                                                   =
                                                                   let uu____3050
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____3051
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____3050
                                                                    uu____3051
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____3049)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____3044
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____2967
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____3066
                                                                  =
                                                                  let uu____3067
                                                                    =
                                                                    let uu____3068
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____3068
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____3067
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____3066);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____3070
                                                                    =
                                                                    let uu____3071
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____3071.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____3070
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____3096
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____3096
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____3103
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____3103
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____3123
                                                                    =
                                                                    let uu____3124
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____3124]
                                                                     in
                                                                    let uu____3125
                                                                    =
                                                                    let uu____3136
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____3136]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____3123;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____3125;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____3161
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____3161))
                                                                  | uu____3164
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____3165
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
                                                                    let uu____3185
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____3185))
                                                                   in
                                                                match uu____3165
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
                                                                    let uu___372_3204
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___372_3204.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___372_3204.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___372_3204.FStar_Syntax_Syntax.action_params);
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
                                match uu____1898 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____3228 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____3228
                                       in
                                    let uu____3231 =
                                      let uu____3236 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____3236 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____3255 ->
                                               let uu____3258 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____3264 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____3264 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____3258
                                               then (gen_univs, t)
                                               else
                                                 (let uu____3270 =
                                                    let uu____3275 =
                                                      let uu____3276 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____3277 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____3276 uu____3277
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____3275)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____3270
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____3231 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____3285 =
                                             let uu____3298 =
                                               let uu____3299 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____3299.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____3298)  in
                                           match uu____3285 with
                                           | ([],uu____3310) -> t
                                           | (uu____3325,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____3326,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____3364 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____3389 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____3389
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____3396 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____3398 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____3398))
                                                && (m <> n1)
                                               in
                                            if uu____3396
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____3416 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____3423 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____3424 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____3416 uu____3423
                                                  uu____3424
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____3436 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____3436 with
                                           | (univs2,defn) ->
                                               let uu____3451 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____3451 with
                                                | (univs',typ) ->
                                                    let uu___373_3467 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___373_3467.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___373_3467.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___373_3467.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___374_3470 = ed2  in
                                           let uu____3471 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____3472 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____3473 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____3474 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____3475 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____3476 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____3477 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____3478 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____3479 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____3480 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____3481 =
                                             let uu____3482 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____3482
                                              in
                                           let uu____3499 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____3500 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____3501 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___374_3470.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___374_3470.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____3471;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____3472;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____3473;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____3474;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____3475;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____3476;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____3477;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____3478;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____3479;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____3480;
                                             FStar_Syntax_Syntax.repr =
                                               uu____3481;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____3499;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____3500;
                                             FStar_Syntax_Syntax.actions =
                                               uu____3501;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___374_3470.FStar_Syntax_Syntax.eff_attrs)
                                           }  in
                                         ((let uu____3505 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____3505
                                           then
                                             let uu____3506 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____3506
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
      let uu____3528 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____3528 with
      | (effect_binders_un,signature_un) ->
          let uu____3545 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____3545 with
           | (effect_binders,env1,uu____3564) ->
               let uu____3565 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____3565 with
                | (signature,uu____3581) ->
                    let raise_error1 uu____3596 =
                      match uu____3596 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____3628  ->
                           match uu____3628 with
                           | (bv,qual) ->
                               let uu____3647 =
                                 let uu___375_3648 = bv  in
                                 let uu____3649 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___375_3648.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___375_3648.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____3649
                                 }  in
                               (uu____3647, qual)) effect_binders
                       in
                    let uu____3654 =
                      let uu____3661 =
                        let uu____3662 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____3662.FStar_Syntax_Syntax.n  in
                      match uu____3661 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____3672)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____3704 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____3654 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____3728 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____3728
                           then
                             let uu____3729 =
                               let uu____3732 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____3732  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____3729
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____3778 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____3778 with
                           | (t2,comp,uu____3791) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____3800 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____3800 with
                          | (repr,_comp) ->
                              ((let uu____3824 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3824
                                then
                                  let uu____3825 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____3825
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
                                let uu____3829 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____3831 =
                                    let uu____3832 =
                                      let uu____3833 =
                                        let uu____3850 =
                                          let uu____3861 =
                                            let uu____3870 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____3873 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____3870, uu____3873)  in
                                          [uu____3861]  in
                                        (wp_type, uu____3850)  in
                                      FStar_Syntax_Syntax.Tm_app uu____3833
                                       in
                                    mk1 uu____3832  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____3831
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____3920 =
                                      let uu____3927 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____3927)  in
                                    let uu____3932 =
                                      let uu____3941 =
                                        let uu____3948 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____3948
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____3941]  in
                                    uu____3920 :: uu____3932  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____3984 =
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
                                  let uu____4047 = item  in
                                  match uu____4047 with
                                  | (u_item,item1) ->
                                      let uu____4062 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____4062 with
                                       | (item2,item_comp) ->
                                           ((let uu____4078 =
                                               let uu____4079 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____4079
                                                in
                                             if uu____4078
                                             then
                                               let uu____4080 =
                                                 let uu____4085 =
                                                   let uu____4086 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____4087 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____4086 uu____4087
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____4085)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____4080
                                             else ());
                                            (let uu____4089 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____4089 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____4107 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____4108 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____4109 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____4109 with
                                | (dmff_env1,uu____4135,bind_wp,bind_elab) ->
                                    let uu____4138 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____4138 with
                                     | (dmff_env2,uu____4164,return_wp,return_elab)
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
                                           let uu____4173 =
                                             let uu____4174 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4174.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4173 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4232 =
                                                 let uu____4251 =
                                                   let uu____4256 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____4256
                                                    in
                                                 match uu____4251 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____4338 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____4232 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____4391 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____4391 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____4414 =
                                                          let uu____4415 =
                                                            let uu____4432 =
                                                              let uu____4443
                                                                =
                                                                let uu____4452
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____4457
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____4452,
                                                                  uu____4457)
                                                                 in
                                                              [uu____4443]
                                                               in
                                                            (wp_type,
                                                              uu____4432)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4415
                                                           in
                                                        mk1 uu____4414  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____4492 =
                                                      let uu____4501 =
                                                        let uu____4502 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____4502
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____4501
                                                       in
                                                    (match uu____4492 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____4525
                                                           =
                                                           let error_msg =
                                                             let uu____4527 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____4528 =
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
                                                               uu____4527
                                                               uu____4528
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
                                                               ((let uu____4533
                                                                   =
                                                                   let uu____4534
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____4534
                                                                    in
                                                                 if
                                                                   uu____4533
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____4536
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
                                                                   uu____4536
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
                                                             let uu____4563 =
                                                               let uu____4568
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____4569
                                                                 =
                                                                 let uu____4570
                                                                   =
                                                                   let uu____4579
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____4579,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____4570]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____4568
                                                                 uu____4569
                                                                in
                                                             uu____4563
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____4616 =
                                                             let uu____4617 =
                                                               let uu____4626
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____4626]
                                                                in
                                                             b11 ::
                                                               uu____4617
                                                              in
                                                           let uu____4651 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____4616
                                                             uu____4651
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____4654 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____4660 =
                                             let uu____4661 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____4661.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4660 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____4719 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____4719
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____4740 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____4746 =
                                             let uu____4747 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____4747.FStar_Syntax_Syntax.n
                                              in
                                           match uu____4746 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____4780 =
                                                 let uu____4781 =
                                                   let uu____4790 =
                                                     let uu____4797 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____4797
                                                      in
                                                   [uu____4790]  in
                                                 FStar_List.append uu____4781
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____4780 body what
                                           | uu____4816 ->
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
                                             (let uu____4840 =
                                                let uu____4841 =
                                                  let uu____4842 =
                                                    let uu____4859 =
                                                      let uu____4870 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____4870
                                                       in
                                                    (t, uu____4859)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____4842
                                                   in
                                                mk1 uu____4841  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____4840)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____4914 = f a2  in
                                               [uu____4914]
                                           | x::xs ->
                                               let uu____4919 =
                                                 apply_last1 f xs  in
                                               x :: uu____4919
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
                                           let uu____4945 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____4945 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____4975 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____4975
                                                 then
                                                   let uu____4976 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____4976
                                                 else ());
                                                (let uu____4978 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____4978))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____4987 =
                                                 let uu____4992 = mk_lid name
                                                    in
                                                 let uu____4993 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____4992 uu____4993
                                                  in
                                               (match uu____4987 with
                                                | (sigelt,fv) ->
                                                    ((let uu____4997 =
                                                        let uu____5000 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____5000
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____4997);
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
                                          (let uu____5105 =
                                             let uu____5108 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____5109 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____5108 :: uu____5109  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____5105);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____5215 =
                                               let uu____5218 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____5219 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____5218 :: uu____5219  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____5215);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____5322 =
                                                FStar_List.fold_left
                                                  (fun uu____5362  ->
                                                     fun action  ->
                                                       match uu____5362 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____5383 =
                                                             let uu____5390 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____5390
                                                               params_un
                                                              in
                                                           (match uu____5383
                                                            with
                                                            | (action_params,env',uu____5399)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____5425
                                                                     ->
                                                                    match uu____5425
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____5444
                                                                    =
                                                                    let uu___376_5445
                                                                    = bv  in
                                                                    let uu____5446
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___376_5445.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___376_5445.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____5446
                                                                    }  in
                                                                    (uu____5444,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____5452
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____5452
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
                                                                    uu____5490
                                                                    ->
                                                                    let uu____5491
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____5491
                                                                     in
                                                                    ((
                                                                    let uu____5495
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____5495
                                                                    then
                                                                    let uu____5496
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____5497
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____5498
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____5499
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____5496
                                                                    uu____5497
                                                                    uu____5498
                                                                    uu____5499
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
                                                                    let uu____5503
                                                                    =
                                                                    let uu____5506
                                                                    =
                                                                    let uu___377_5507
                                                                    = action
                                                                     in
                                                                    let uu____5508
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____5509
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___377_5507.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___377_5507.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___377_5507.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____5508;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____5509
                                                                    }  in
                                                                    uu____5506
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____5503))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____5322 with
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
                                                      let uu____5552 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____5559 =
                                                        let uu____5568 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____5568]  in
                                                      uu____5552 ::
                                                        uu____5559
                                                       in
                                                    let uu____5593 =
                                                      let uu____5596 =
                                                        let uu____5597 =
                                                          let uu____5598 =
                                                            let uu____5615 =
                                                              let uu____5626
                                                                =
                                                                let uu____5635
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____5638
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____5635,
                                                                  uu____5638)
                                                                 in
                                                              [uu____5626]
                                                               in
                                                            (repr,
                                                              uu____5615)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____5598
                                                           in
                                                        mk1 uu____5597  in
                                                      let uu____5673 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____5596
                                                        uu____5673
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____5593
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____5674 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____5676 =
                                                    let uu____5685 =
                                                      let uu____5686 =
                                                        let uu____5689 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____5689
                                                         in
                                                      uu____5686.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5685 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____5703)
                                                        ->
                                                        let uu____5740 =
                                                          let uu____5761 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____5761
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____5829 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____5740
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____5893 =
                                                               let uu____5894
                                                                 =
                                                                 let uu____5897
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____5897
                                                                  in
                                                               uu____5894.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____5893
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____5930
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____5930
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____5945
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____5976
                                                                     ->
                                                                    match uu____5976
                                                                    with
                                                                    | 
                                                                    (bv,uu____5984)
                                                                    ->
                                                                    let uu____5989
                                                                    =
                                                                    let uu____5990
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5990
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5989
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____5945
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
                                                                    let uu____6078
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____6078
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____6085
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____6095
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____6095
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____6102
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____6105
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____6102,
                                                                    uu____6105)))
                                                              | uu____6120 ->
                                                                  let uu____6121
                                                                    =
                                                                    let uu____6126
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
                                                                    uu____6126)
                                                                     in
                                                                  raise_error1
                                                                    uu____6121))
                                                    | uu____6136 ->
                                                        let uu____6137 =
                                                          let uu____6142 =
                                                            let uu____6143 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____6143
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____6142)
                                                           in
                                                        raise_error1
                                                          uu____6137
                                                     in
                                                  (match uu____5676 with
                                                   | (pre,post) ->
                                                       ((let uu____6173 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____6175 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____6177 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___378_6179
                                                             = ed  in
                                                           let uu____6180 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____6181 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____6182 =
                                                             let uu____6183 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____6183)
                                                              in
                                                           let uu____6190 =
                                                             let uu____6191 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____6191)
                                                              in
                                                           let uu____6198 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____6199 =
                                                             let uu____6200 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____6200)
                                                              in
                                                           let uu____6207 =
                                                             let uu____6208 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____6208)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____6180;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____6181;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____6182;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____6190;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____6198;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____6199;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____6207;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___378_6179.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____6215 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____6215
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____6233
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____6233
                                                               then
                                                                 let uu____6234
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____6234
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
                                                                    let uu____6248
                                                                    =
                                                                    let uu____6251
                                                                    =
                                                                    let uu____6252
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____6252)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____6251
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
                                                                    uu____6248;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____6259
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____6259
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____6261
                                                                 =
                                                                 let uu____6264
                                                                   =
                                                                   let uu____6267
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____6267
                                                                    in
                                                                 FStar_List.append
                                                                   uu____6264
                                                                   sigelts'
                                                                  in
                                                               (uu____6261,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____6333 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6333 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6368 = FStar_List.hd ses  in
            uu____6368.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6373 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6377,[],t,uu____6379,uu____6380);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6382;
               FStar_Syntax_Syntax.sigattrs = uu____6383;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6385,_t_top,_lex_t_top,_0_16,uu____6388);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6390;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6391;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6393,_t_cons,_lex_t_cons,_0_17,uu____6396);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6398;
                 FStar_Syntax_Syntax.sigattrs = uu____6399;_}::[]
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
                 let uu____6448 =
                   let uu____6455 =
                     let uu____6456 =
                       let uu____6463 =
                         let uu____6466 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6466
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6463, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6456  in
                   FStar_Syntax_Syntax.mk uu____6455  in
                 uu____6448 FStar_Pervasives_Native.None r1  in
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
                   let uu____6482 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6482
                    in
                 let hd1 =
                   let uu____6484 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6484
                    in
                 let tl1 =
                   let uu____6486 =
                     let uu____6487 =
                       let uu____6494 =
                         let uu____6495 =
                           let uu____6502 =
                             let uu____6505 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6505
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6502, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6495  in
                       FStar_Syntax_Syntax.mk uu____6494  in
                     uu____6487 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6486
                    in
                 let res =
                   let uu____6514 =
                     let uu____6521 =
                       let uu____6522 =
                         let uu____6529 =
                           let uu____6532 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6532
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6529,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6522  in
                     FStar_Syntax_Syntax.mk uu____6521  in
                   uu____6514 FStar_Pervasives_Native.None r2  in
                 let uu____6538 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6538
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
               let uu____6575 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6575;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6580 ->
               let err_msg =
                 let uu____6584 =
                   let uu____6585 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6585  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6584
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
    fun uu____6607  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6607 with
          | (uvs,t) ->
              let uu____6620 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6620 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6631 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6631 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6648 =
                        let uu____6651 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____6651
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____6648)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6673 =
          let uu____6674 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6674 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6673 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6698 =
          let uu____6699 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6699 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6698 r
  
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
          (let uu____6748 =
             FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
           if uu____6748
           then
             let uu____6749 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6749
           else ());
          (let uu____6751 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness
               env1 ses quals lids
              in
           match uu____6751 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____6782 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env1 tcs) datas
                    in
                 FStar_All.pipe_right uu____6782 FStar_List.flatten  in
               ((let uu____6796 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6798 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      Prims.op_Negation uu____6798)
                    in
                 if uu____6796
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
                           let uu____6809 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____6819,uu____6820,uu____6821,uu____6822,uu____6823)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6832 -> failwith "Impossible!"  in
                           match uu____6809 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs));
                (let skip_prims_type uu____6845 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____6849,uu____6850,uu____6851,uu____6852,uu____6853)
                         -> lid
                     | uu____6862 -> failwith "Impossible"  in
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
                   let uu____6875 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env1.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____6875
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
                 (let uu____6897 =
                    FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                  ());
                 res)))
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____6904 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____6904 en  in
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
      | uu____7134 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7182 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7182 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7201 .
    'Auu____7201 FStar_Pervasives_Native.option -> 'Auu____7201 Prims.list
  =
  fun uu___358_7210  ->
    match uu___358_7210 with
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
      | uu____7254 ->
          let rec collect1 l =
            match l with
            | [] -> []
            | hd1::tl1 ->
                let uu____7286 = collect1 tl1  in
                (match uu____7286 with
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
            | ((e,n1)::uu____7471,[]) ->
                FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
            | ([],(e,n1)::uu____7506) ->
                FStar_Pervasives_Native.Some (e, (Prims.parse_int "0"), n1)
            | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 <> hd2 ->
                FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
            | ((hd1,n1)::tl1,(hd2,n2)::tl2) ->
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2
             in
          aux l11 l21
  
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____7672 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____7697 ->
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
             let uu____7752 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____7752
             then
               let ses1 =
                 let uu____7758 =
                   let uu____7759 =
                     let uu____7760 =
                       tc_inductive
                         (let uu___379_7769 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___379_7769.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___379_7769.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___379_7769.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___379_7769.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___379_7769.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___379_7769.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___379_7769.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___379_7769.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___379_7769.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___379_7769.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___379_7769.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___379_7769.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___379_7769.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___379_7769.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___379_7769.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___379_7769.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___379_7769.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___379_7769.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___379_7769.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___379_7769.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___379_7769.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___379_7769.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___379_7769.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___379_7769.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___379_7769.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___379_7769.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___379_7769.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___379_7769.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___379_7769.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___379_7769.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___379_7769.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___379_7769.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___379_7769.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___379_7769.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___379_7769.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___379_7769.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___379_7769.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___379_7769.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___379_7769.FStar_TypeChecker_Env.dep_graph)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____7760
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____7759
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____7758
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____7781 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____7781
                 then
                   let uu____7782 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___380_7785 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___380_7785.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___380_7785.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___380_7785.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___380_7785.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____7782
                 else ());
                ses1)
             else ses  in
           let uu____7792 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____7792 with
            | (sigbndle,projectors_ses) -> ([sigbndle], projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____7824 = cps_and_elaborate env ne  in
           (match uu____7824 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___381_7861 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___381_7861.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___381_7861.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___381_7861.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___381_7861.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___382_7863 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___382_7863.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___382_7863.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___382_7863.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___382_7863.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 =
             let uu____7870 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env)
                in
             if uu____7870
             then
               let ne1 =
                 let uu____7872 =
                   let uu____7873 =
                     let uu____7874 =
                       tc_eff_decl
                         (let uu___383_7877 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___383_7877.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___383_7877.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___383_7877.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___383_7877.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___383_7877.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___383_7877.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___383_7877.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___383_7877.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___383_7877.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___383_7877.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___383_7877.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___383_7877.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___383_7877.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___383_7877.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___383_7877.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___383_7877.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___383_7877.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___383_7877.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___383_7877.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___383_7877.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___383_7877.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___383_7877.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___383_7877.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___383_7877.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___383_7877.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___383_7877.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___383_7877.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___383_7877.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___383_7877.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___383_7877.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___383_7877.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___383_7877.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___383_7877.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___383_7877.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___383_7877.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___383_7877.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___383_7877.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___383_7877.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___383_7877.FStar_TypeChecker_Env.dep_graph)
                          }) ne
                        in
                     FStar_All.pipe_right uu____7874
                       (fun ne1  ->
                          let uu___384_7881 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___384_7881.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___384_7881.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___384_7881.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___384_7881.FStar_Syntax_Syntax.sigattrs)
                          })
                      in
                   FStar_All.pipe_right uu____7873
                     (FStar_TypeChecker_Normalize.elim_uvars env)
                    in
                 FStar_All.pipe_right uu____7872
                   FStar_Syntax_Util.eff_decl_of_new_effect
                  in
               ((let uu____7883 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____7883
                 then
                   let uu____7884 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___385_7887 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___385_7887.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___385_7887.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___385_7887.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___385_7887.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Effect decl after phase 1: %s\n"
                     uu____7884
                 else ());
                ne1)
             else ne  in
           let ne2 = tc_eff_decl env ne1  in
           let se1 =
             let uu___386_7892 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
               FStar_Syntax_Syntax.sigrng =
                 (uu___386_7892.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___386_7892.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___386_7892.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___386_7892.FStar_Syntax_Syntax.sigattrs)
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
           let uu____7900 =
             let uu____7907 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____7907
              in
           (match uu____7900 with
            | (a,wp_a_src) ->
                let uu____7922 =
                  let uu____7929 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____7929
                   in
                (match uu____7922 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____7945 =
                         let uu____7948 =
                           let uu____7949 =
                             let uu____7956 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____7956)  in
                           FStar_Syntax_Syntax.NT uu____7949  in
                         [uu____7948]  in
                       FStar_Syntax_Subst.subst uu____7945 wp_b_tgt  in
                     let expected_k =
                       let uu____7964 =
                         let uu____7973 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____7980 =
                           let uu____7989 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____7989]  in
                         uu____7973 :: uu____7980  in
                       let uu____8014 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____7964 uu____8014  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____8043 =
                           let uu____8048 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____8048)
                            in
                         let uu____8049 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____8043 uu____8049  in
                       let uu____8052 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____8052 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____8086 =
                             let uu____8087 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____8087  in
                           if uu____8086
                           then no_reify eff_name
                           else
                             (let uu____8093 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____8094 =
                                let uu____8101 =
                                  let uu____8102 =
                                    let uu____8119 =
                                      let uu____8130 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____8139 =
                                        let uu____8150 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____8150]  in
                                      uu____8130 :: uu____8139  in
                                    (repr, uu____8119)  in
                                  FStar_Syntax_Syntax.Tm_app uu____8102  in
                                FStar_Syntax_Syntax.mk uu____8101  in
                              uu____8094 FStar_Pervasives_Native.None
                                uu____8093)
                        in
                     let uu____8198 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____8370 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____8379 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____8379 with
                               | (usubst,uvs1) ->
                                   let uu____8402 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____8403 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____8402, uu____8403)
                             else (env, lift_wp)  in
                           (match uu____8370 with
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
                                     let uu____8448 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____8448))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____8519 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____8532 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____8532 with
                               | (usubst,uvs) ->
                                   let uu____8557 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____8557)
                             else ([], lift)  in
                           (match uu____8519 with
                            | (uvs,lift1) ->
                                ((let uu____8592 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____8592
                                  then
                                    let uu____8593 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____8593
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____8596 =
                                    let uu____8603 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____8603 lift1
                                     in
                                  match uu____8596 with
                                  | (lift2,comp,uu____8628) ->
                                      let uu____8629 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____8629 with
                                       | (uu____8658,lift_wp,lift_elab) ->
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
                                             let uu____8685 =
                                               let uu____8696 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8696
                                                in
                                             let uu____8713 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____8685, uu____8713)
                                           else
                                             (let uu____8741 =
                                                let uu____8752 =
                                                  let uu____8761 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____8761)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____8752
                                                 in
                                              let uu____8776 =
                                                let uu____8785 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____8785)  in
                                              (uu____8741, uu____8776))))))
                        in
                     (match uu____8198 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___387_8857 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___387_8857.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___387_8857.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___387_8857.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___387_8857.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___387_8857.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___387_8857.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___387_8857.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___387_8857.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___387_8857.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___387_8857.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___387_8857.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___387_8857.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___387_8857.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___387_8857.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___387_8857.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___387_8857.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___387_8857.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___387_8857.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___387_8857.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___387_8857.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___387_8857.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___387_8857.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___387_8857.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___387_8857.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___387_8857.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___387_8857.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___387_8857.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___387_8857.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___387_8857.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___387_8857.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___387_8857.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___387_8857.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___387_8857.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___387_8857.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___387_8857.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___387_8857.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___387_8857.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___387_8857.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___387_8857.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___387_8857.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____8889 =
                                  let uu____8894 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____8894 with
                                  | (usubst,uvs1) ->
                                      let uu____8917 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____8918 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____8917, uu____8918)
                                   in
                                (match uu____8889 with
                                 | (env2,lift2) ->
                                     let uu____8923 =
                                       let uu____8930 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____8930
                                        in
                                     (match uu____8923 with
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
                                              let uu____8956 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____8957 =
                                                let uu____8964 =
                                                  let uu____8965 =
                                                    let uu____8982 =
                                                      let uu____8993 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____9002 =
                                                        let uu____9013 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____9013]  in
                                                      uu____8993 ::
                                                        uu____9002
                                                       in
                                                    (lift_wp1, uu____8982)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____8965
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____8964
                                                 in
                                              uu____8957
                                                FStar_Pervasives_Native.None
                                                uu____8956
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____9064 =
                                              let uu____9073 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____9080 =
                                                let uu____9089 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____9096 =
                                                  let uu____9105 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____9105]  in
                                                uu____9089 :: uu____9096  in
                                              uu____9073 :: uu____9080  in
                                            let uu____9136 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____9064 uu____9136
                                             in
                                          let uu____9139 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____9139 with
                                           | (expected_k2,uu____9149,uu____9150)
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
                                                        env2 lift2
                                                        expected_k2
                                                       in
                                                    let uu____9154 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____9154))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____9162 =
                              let uu____9163 =
                                let uu____9164 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9164
                                  FStar_List.length
                                 in
                              uu____9163 <> (Prims.parse_int "1")  in
                            if uu____9162
                            then
                              let uu____9183 =
                                let uu____9188 =
                                  let uu____9189 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9190 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9191 =
                                    let uu____9192 =
                                      let uu____9193 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9193
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9192
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9189 uu____9190 uu____9191
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9188)
                                 in
                              FStar_Errors.raise_error uu____9183 r
                            else ());
                           (let uu____9214 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____9216 =
                                   let uu____9217 =
                                     let uu____9220 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____9220
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9217
                                     FStar_List.length
                                    in
                                 uu____9216 <> (Prims.parse_int "1"))
                               in
                            if uu____9214
                            then
                              let uu____9255 =
                                let uu____9260 =
                                  let uu____9261 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9262 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9263 =
                                    let uu____9264 =
                                      let uu____9265 =
                                        let uu____9268 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____9268
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9265
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9264
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9261 uu____9262 uu____9263
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9260)
                                 in
                              FStar_Errors.raise_error uu____9255 r
                            else ());
                           (let sub2 =
                              let uu___388_9305 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___388_9305.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___388_9305.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___389_9307 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___389_9307.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___389_9307.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___389_9307.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___389_9307.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], []))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env  in
           let uu____9322 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____9346 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____9346 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____9377 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____9377 c  in
                    let uu____9386 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____9386, uvs1, tps1, c1))
              in
           (match uu____9322 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____9406 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____9406 with
                 | (tps2,c2) ->
                     let uu____9421 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____9421 with
                      | (tps3,env3,us) ->
                          let uu____9439 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____9439 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____9460 =
                                   let uu____9461 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____9461
                                    in
                                 match uu____9460 with
                                 | (uvs2,t) ->
                                     let uu____9490 =
                                       let uu____9495 =
                                         let uu____9508 =
                                           let uu____9509 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____9509.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____9508)  in
                                       match uu____9495 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____9524,c5)) -> ([], c5)
                                       | (uu____9566,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____9605 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____9490 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____9633 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____9633 with
                                              | (uu____9638,t1) ->
                                                  let uu____9640 =
                                                    let uu____9645 =
                                                      let uu____9646 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____9647 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____9648 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____9646 uu____9647
                                                        uu____9648
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____9645)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____9640 r)
                                           else ();
                                           (let se1 =
                                              let uu___390_9651 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___390_9651.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___390_9651.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___390_9651.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___390_9651.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____9658,uu____9659,uu____9660) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___359_9664  ->
                   match uu___359_9664 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____9665 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____9670,uu____9671) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___359_9679  ->
                   match uu___359_9679 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____9680 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____9690 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____9690
             then
               let uu____9691 =
                 let uu____9696 =
                   let uu____9697 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____9697
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____9696)
                  in
               FStar_Errors.raise_error uu____9691 r
             else ());
            (let uu____9699 =
               let uu____9708 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____9708
               then
                 let uu____9717 =
                   tc_declare_typ
                     (let uu___391_9720 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___391_9720.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___391_9720.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___391_9720.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___391_9720.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___391_9720.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___391_9720.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___391_9720.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___391_9720.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___391_9720.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___391_9720.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___391_9720.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___391_9720.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___391_9720.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___391_9720.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___391_9720.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___391_9720.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___391_9720.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___391_9720.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___391_9720.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___391_9720.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___391_9720.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___391_9720.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___391_9720.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___391_9720.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___391_9720.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___391_9720.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___391_9720.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___391_9720.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___391_9720.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___391_9720.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___391_9720.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___391_9720.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___391_9720.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___391_9720.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___391_9720.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___391_9720.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___391_9720.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___391_9720.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___391_9720.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___391_9720.FStar_TypeChecker_Env.dep_graph)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____9717 with
                 | (uvs1,t1) ->
                     ((let uu____9744 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____9744
                       then
                         let uu____9745 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____9746 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____9745 uu____9746
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____9699 with
             | (uvs1,t1) ->
                 let uu____9775 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____9775 with
                  | (uvs2,t2) ->
                      ([(let uu___392_9803 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___392_9803.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___392_9803.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___392_9803.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___392_9803.FStar_Syntax_Syntax.sigattrs)
                         })], []))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____9808 =
             let uu____9817 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____9817
             then
               let uu____9826 =
                 tc_assume
                   (let uu___393_9829 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___393_9829.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___393_9829.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___393_9829.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___393_9829.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___393_9829.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___393_9829.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___393_9829.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___393_9829.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___393_9829.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___393_9829.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___393_9829.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___393_9829.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___393_9829.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___393_9829.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___393_9829.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___393_9829.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___393_9829.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___393_9829.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___393_9829.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___393_9829.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___393_9829.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___393_9829.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___393_9829.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___393_9829.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___393_9829.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___393_9829.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___393_9829.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___393_9829.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___393_9829.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___393_9829.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___393_9829.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___393_9829.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___393_9829.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___393_9829.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___393_9829.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___393_9829.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___393_9829.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___393_9829.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___393_9829.FStar_TypeChecker_Env.dep_graph)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____9826 with
               | (uvs1,t1) ->
                   ((let uu____9853 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____9853
                     then
                       let uu____9854 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9855 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____9854
                         uu____9855
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____9808 with
            | (uvs1,t1) ->
                let uu____9884 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____9884 with
                 | (uvs2,t2) ->
                     ([(let uu___394_9912 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___394_9912.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___394_9912.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___394_9912.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___394_9912.FStar_Syntax_Syntax.sigattrs)
                        })], [])))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____9916 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____9916 with
            | (e1,c,g1) ->
                let uu____9934 =
                  let uu____9941 =
                    let uu____9944 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____9944  in
                  let uu____9945 =
                    let uu____9950 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____9950)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____9941 uu____9945
                   in
                (match uu____9934 with
                 | (e2,uu____9960,g) ->
                     ((let uu____9963 = FStar_TypeChecker_Env.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____9963);
                      (let se1 =
                         let uu___395_9965 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___395_9965.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___395_9965.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___395_9965.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___395_9965.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____9977 = FStar_Options.debug_any ()  in
             if uu____9977
             then
               let uu____9978 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____9979 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____9978
                 uu____9979
             else ());
            (let ses = env.FStar_TypeChecker_Env.splice env t  in
             let lids' =
               FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses  in
             FStar_List.iter
               (fun lid  ->
                  let uu____9992 =
                    FStar_List.tryFind (FStar_Ident.lid_equals lid) lids'  in
                  match uu____9992 with
                  | FStar_Pervasives_Native.Some uu____9995 -> ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____9996 =
                        let uu____10001 =
                          let uu____10002 = FStar_Ident.string_of_lid lid  in
                          let uu____10003 =
                            let uu____10004 =
                              FStar_List.map FStar_Ident.string_of_lid lids'
                               in
                            FStar_All.pipe_left (FStar_String.concat ", ")
                              uu____10004
                             in
                          FStar_Util.format2
                            "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                            uu____10002 uu____10003
                           in
                        (FStar_Errors.Fatal_SplicedUndef, uu____10001)  in
                      FStar_Errors.raise_error uu____9996 r) lids;
             ([], ses)))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let drop_logic =
                   FStar_List.filter
                     (fun x  ->
                        Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                    in
                 let uu____10076 =
                   let uu____10085 = drop_logic q  in
                   let uu____10088 = drop_logic q'  in
                   (uu____10085, uu____10088)  in
                 (match uu____10076 with
                  | (q1,q'1) ->
                      let uu____10109 =
                        ((FStar_List.length q1) = (FStar_List.length q'1)) &&
                          (FStar_List.forall2
                             FStar_Syntax_Util.qualifier_equal q1 q'1)
                         in
                      if uu____10109
                      then FStar_Pervasives_Native.Some q1
                      else
                        (let uu____10117 =
                           let uu____10122 =
                             let uu____10123 =
                               FStar_Syntax_Print.lid_to_string l  in
                             let uu____10124 =
                               FStar_Syntax_Print.quals_to_string q1  in
                             let uu____10125 =
                               FStar_Syntax_Print.quals_to_string q'1  in
                             FStar_Util.format3
                               "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                               uu____10123 uu____10124 uu____10125
                              in
                           (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                             uu____10122)
                            in
                         FStar_Errors.raise_error uu____10117 r))
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____10159 =
                   let uu____10160 = FStar_Syntax_Subst.compress def  in
                   uu____10160.FStar_Syntax_Syntax.n  in
                 match uu____10159 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____10172,uu____10173) -> binders
                 | uu____10198 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____10210;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____10314) -> val_bs1
                     | (uu____10345,[]) -> val_bs1
                     | ((body_bv,uu____10377)::bt,(val_bv,aqual)::vt) ->
                         let uu____10434 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____10456) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___396_10462 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___397_10465 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___397_10465.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___396_10462.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___396_10462.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____10434
                      in
                   let uu____10468 =
                     let uu____10475 =
                       let uu____10476 =
                         let uu____10491 = rename_binders1 def_bs val_bs  in
                         (uu____10491, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____10476  in
                     FStar_Syntax_Syntax.mk uu____10475  in
                   uu____10468 FStar_Pervasives_Native.None r1
               | uu____10513 -> typ1  in
             let uu___398_10514 = lb  in
             let uu____10515 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___398_10514.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___398_10514.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____10515;
               FStar_Syntax_Syntax.lbeff =
                 (uu___398_10514.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___398_10514.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___398_10514.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___398_10514.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____10518 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____10569  ->
                     fun lb  ->
                       match uu____10569 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____10611 =
                             let uu____10622 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____10622 with
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
                                   | uu____10695 ->
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
                                  (let uu____10738 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def,
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____10738, quals_opt1)))
                              in
                           (match uu____10611 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____10518 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____10826 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___360_10830  ->
                                match uu___360_10830 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____10831 -> false))
                         in
                      if uu____10826
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____10841 =
                    let uu____10848 =
                      let uu____10849 =
                        let uu____10862 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____10862)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____10849  in
                    FStar_Syntax_Syntax.mk uu____10848  in
                  uu____10841 FStar_Pervasives_Native.None r  in
                let env0 =
                  let uu___399_10881 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___399_10881.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___399_10881.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___399_10881.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___399_10881.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___399_10881.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___399_10881.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___399_10881.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___399_10881.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___399_10881.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___399_10881.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___399_10881.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___399_10881.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___399_10881.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___399_10881.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___399_10881.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___399_10881.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___399_10881.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___399_10881.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___399_10881.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___399_10881.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___399_10881.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___399_10881.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___399_10881.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___399_10881.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___399_10881.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___399_10881.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___399_10881.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___399_10881.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___399_10881.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___399_10881.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___399_10881.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___399_10881.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___399_10881.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___399_10881.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___399_10881.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___399_10881.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___399_10881.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___399_10881.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___399_10881.FStar_TypeChecker_Env.dep_graph)
                  }  in
                let e1 =
                  let uu____10883 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env0)
                     in
                  if uu____10883
                  then
                    let drop_lbtyp e_lax =
                      let uu____10890 =
                        let uu____10891 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____10891.FStar_Syntax_Syntax.n  in
                      match uu____10890 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____10909 =
                              let uu____10910 = FStar_Syntax_Subst.compress e
                                 in
                              uu____10910.FStar_Syntax_Syntax.n  in
                            match uu____10909 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____10913,lb1::[]),uu____10915) ->
                                let uu____10928 =
                                  let uu____10929 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____10929.FStar_Syntax_Syntax.n  in
                                (match uu____10928 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____10932 -> false)
                            | uu____10933 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___400_10934 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___401_10946 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___401_10946.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___400_10934.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___400_10934.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____10948 -> e_lax  in
                    let e1 =
                      let uu____10950 =
                        let uu____10951 =
                          let uu____10952 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___402_10961 = env0  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___402_10961.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___402_10961.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___402_10961.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___402_10961.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___402_10961.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___402_10961.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___402_10961.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___402_10961.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___402_10961.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___402_10961.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___402_10961.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___402_10961.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___402_10961.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___402_10961.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___402_10961.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___402_10961.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___402_10961.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___402_10961.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___402_10961.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___402_10961.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___402_10961.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___402_10961.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___402_10961.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___402_10961.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___402_10961.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___402_10961.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___402_10961.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___402_10961.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___402_10961.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___402_10961.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___402_10961.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___402_10961.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___402_10961.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___402_10961.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___402_10961.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___402_10961.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___402_10961.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___402_10961.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___402_10961.FStar_TypeChecker_Env.dep_graph)
                               }) e
                             in
                          FStar_All.pipe_right uu____10952
                            (fun uu____10972  ->
                               match uu____10972 with
                               | (e1,uu____10980,uu____10981) -> e1)
                           in
                        FStar_All.pipe_right uu____10951
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env0)
                         in
                      FStar_All.pipe_right uu____10950 drop_lbtyp  in
                    ((let uu____10983 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____10983
                      then
                        let uu____10984 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____10984
                      else ());
                     e1)
                  else e  in
                let uu____10987 =
                  let uu____10998 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1
                     in
                  match uu____10998 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e2);
                       FStar_Syntax_Syntax.pos = uu____11017;
                       FStar_Syntax_Syntax.vars = uu____11018;_},uu____11019,g)
                      when FStar_TypeChecker_Env.is_trivial g ->
                      let lbs2 =
                        let uu____11046 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____11046)  in
                      let quals1 =
                        match e2.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____11064,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____11069 -> quals  in
                      ((let uu___403_11077 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___403_11077.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___403_11077.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___403_11077.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____11080 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____10987 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              FStar_TypeChecker_Env.insert_fv_info env1 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____11129 = log env1  in
                       if uu____11129
                       then
                         let uu____11130 =
                           let uu____11131 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____11146 =
                                         let uu____11155 =
                                           let uu____11156 =
                                             let uu____11159 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____11159.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____11156.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env1 uu____11155
                                          in
                                       match uu____11146 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____11166 -> false  in
                                     if should_log
                                     then
                                       let uu____11175 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____11176 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____11175 uu____11176
                                     else ""))
                              in
                           FStar_All.pipe_right uu____11131
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____11130
                       else ());
                      ([se1], [])))))
  
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
      (let uu____11213 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____11213
       then
         let uu____11214 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____11214
       else ());
      (let uu____11216 = get_fail_se se  in
       match uu____11216 with
       | FStar_Pervasives_Native.Some (uu____11233,false ) when
           let uu____11244 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____11244 -> ([], [])
       | FStar_Pervasives_Native.Some (errnos,uu____11250) ->
           ((let uu____11262 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____11262
             then
               let uu____11263 =
                 let uu____11264 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____11264
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____11263
             else ());
            (let errs =
               FStar_Errors.catch_errors
                 (fun uu____11282  -> tc_decl' env1 se)
                in
             (let uu____11284 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____11284
              then
                (FStar_Util.print_string ">> Got issues: [\n";
                 FStar_List.iter FStar_Errors.print_issue errs;
                 FStar_Util.print_string ">>]\n")
              else ());
             (let uu____11288 =
                let uu____11303 =
                  let uu____11312 =
                    FStar_List.concatMap
                      (fun i  -> list_of_option i.FStar_Errors.issue_number)
                      errs
                     in
                  check_multi_contained errnos uu____11312  in
                (errs, uu____11303)  in
              match uu____11288 with
              | ([],uu____11335) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   FStar_Errors.raise_error
                     (FStar_Errors.Error_DidNotFail,
                       "This top-level definition was expected to fail, but it succeeded")
                     se.FStar_Syntax_Syntax.sigrng)
              | (uu____11363,FStar_Pervasives_Native.Some (e,n1,n2)) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   (let uu____11386 =
                      let uu____11391 =
                        let uu____11392 = FStar_Util.string_of_int e  in
                        let uu____11393 = FStar_Util.string_of_int n1  in
                        let uu____11394 = FStar_Util.string_of_int n2  in
                        FStar_Util.format3
                          "This top-level definition was expected to raise Error #%s %s times, but it raised it %s times"
                          uu____11392 uu____11393 uu____11394
                         in
                      (FStar_Errors.Error_DidNotFail, uu____11391)  in
                    FStar_Errors.raise_error uu____11386
                      se.FStar_Syntax_Syntax.sigrng))
              | (uu____11403,FStar_Pervasives_Native.None ) -> ([], []))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
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
             (fun uu___361_11475  ->
                match uu___361_11475 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____11476 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____11484) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____11490 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____11499 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____11504 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____11519 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____11544 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11568) ->
          let uu____11577 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____11577
          then
            let for_export_bundle se1 uu____11612 =
              match uu____11612 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____11651,uu____11652) ->
                       let dec =
                         let uu___404_11662 = se1  in
                         let uu____11663 =
                           let uu____11664 =
                             let uu____11671 =
                               let uu____11672 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____11672  in
                             (l, us, uu____11671)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____11664
                            in
                         {
                           FStar_Syntax_Syntax.sigel = uu____11663;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___404_11662.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___404_11662.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___404_11662.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____11682,uu____11683,uu____11684) ->
                       let dec =
                         let uu___405_11690 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___405_11690.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___405_11690.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___405_11690.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____11695 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____11717,uu____11718,uu____11719)
          ->
          let uu____11720 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____11720 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____11741 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____11741
          then
            ([(let uu___406_11757 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___406_11757.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___406_11757.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___406_11757.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____11759 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___362_11763  ->
                       match uu___362_11763 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____11764 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11769 ->
                           true
                       | uu____11770 -> false))
                in
             if uu____11759 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____11788 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____11793 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11798 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11803 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11808 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11826) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11837 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____11837
          then ([], hidden)
          else
            (let dec =
               let uu____11854 = FStar_Ident.range_of_lid lid  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____11854;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }  in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____11865 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____11865
          then
            let uu____11874 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___407_11887 = se  in
                      let uu____11888 =
                        let uu____11889 =
                          let uu____11896 =
                            let uu____11897 =
                              let uu____11900 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____11900.FStar_Syntax_Syntax.fv_name  in
                            uu____11897.FStar_Syntax_Syntax.v  in
                          (uu____11896, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____11889  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____11888;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___407_11887.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___407_11887.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___407_11887.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____11874, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____11921 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____11921
       then
         let uu____11922 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____11922
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____11924 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____11941 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____11956) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____11959 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11960 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____11970 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____11970) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11971,uu____11972,uu____11973) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___363_11977  ->
                   match uu___363_11977 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11978 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____11979,uu____11980) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___363_11988  ->
                   match uu___363_11988 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11989 -> false))
           -> env
       | uu____11990 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____12058 se =
        match uu____12058 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____12111 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____12111
              then
                let uu____12112 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____12112
              else ());
             (let uu____12114 = tc_decl env1 se  in
              match uu____12114 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____12164 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____12164
                             then
                               let uu____12165 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____12165
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
                    (let uu____12188 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____12188
                     then
                       let uu____12189 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____12195 =
                                  let uu____12196 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____12196 "\n"  in
                                Prims.strcat s uu____12195) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____12189
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____12201 =
                       let uu____12210 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____12210
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____12249 se1 =
                            match uu____12249 with
                            | (exports1,hidden1) ->
                                let uu____12277 = for_export hidden1 se1  in
                                (match uu____12277 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____12201 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___408_12356 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___408_12356.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___408_12356.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___408_12356.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___408_12356.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____12438 = acc  in
        match uu____12438 with
        | (uu____12473,uu____12474,env1,uu____12476) ->
            let uu____12489 =
              FStar_Util.record_time
                (fun uu____12535  -> process_one_decl acc se)
               in
            (match uu____12489 with
             | (r,ms_elapsed) ->
                 ((let uu____12599 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____12599
                   then
                     let uu____12600 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____12601 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____12600 uu____12601
                   else ());
                  r))
         in
      let uu____12603 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____12603 with
      | (ses1,exports,env1,uu____12651) ->
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
          let uu___409_12688 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___409_12688.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___409_12688.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___409_12688.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___409_12688.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___409_12688.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___409_12688.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___409_12688.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___409_12688.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___409_12688.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___409_12688.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___409_12688.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___409_12688.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___409_12688.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___409_12688.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___409_12688.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___409_12688.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___409_12688.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___409_12688.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___409_12688.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___409_12688.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___409_12688.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___409_12688.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___409_12688.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___409_12688.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___409_12688.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___409_12688.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___409_12688.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___409_12688.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___409_12688.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___409_12688.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___409_12688.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___409_12688.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___409_12688.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___409_12688.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___409_12688.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___409_12688.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___409_12688.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___409_12688.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____12705 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____12705 with
          | (univs2,t1) ->
              ((let uu____12713 =
                  let uu____12714 =
                    let uu____12719 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____12719  in
                  FStar_All.pipe_left uu____12714
                    (FStar_Options.Other "Exports")
                   in
                if uu____12713
                then
                  let uu____12720 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____12721 =
                    let uu____12722 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____12722
                      (FStar_String.concat ", ")
                     in
                  let uu____12733 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____12720 uu____12721 uu____12733
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____12736 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____12736 (fun a237  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____12762 =
             let uu____12763 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____12764 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____12763 uu____12764
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____12762);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12773) ->
              let uu____12782 =
                let uu____12783 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____12783  in
              if uu____12782
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____12793,uu____12794) ->
              let t =
                let uu____12806 =
                  let uu____12813 =
                    let uu____12814 =
                      let uu____12829 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____12829)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____12814  in
                  FStar_Syntax_Syntax.mk uu____12813  in
                uu____12806 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____12848,uu____12849,uu____12850) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____12858 =
                let uu____12859 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____12859  in
              if uu____12858 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____12863,lbs),uu____12865) ->
              let uu____12874 =
                let uu____12875 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____12875  in
              if uu____12874
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
              let uu____12894 =
                let uu____12895 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____12895  in
              if uu____12894
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____12912 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____12913 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12920 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12921 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____12922 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____12923 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____12930 -> ()  in
        let uu____12931 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____12931 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____13026) -> true
             | uu____13027 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____13056 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____13095 ->
                   let uu____13096 =
                     let uu____13103 =
                       let uu____13104 =
                         let uu____13119 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____13119)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____13104  in
                     FStar_Syntax_Syntax.mk uu____13103  in
                   uu____13096 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____13139,uu____13140) ->
            let s1 =
              let uu___410_13150 = s  in
              let uu____13151 =
                let uu____13152 =
                  let uu____13159 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____13159)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____13152  in
              let uu____13160 =
                let uu____13163 =
                  let uu____13166 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____13166  in
                FStar_Syntax_Syntax.Assumption :: uu____13163  in
              {
                FStar_Syntax_Syntax.sigel = uu____13151;
                FStar_Syntax_Syntax.sigrng =
                  (uu___410_13150.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____13160;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___410_13150.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___410_13150.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____13169 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____13193 lbdef =
        match uu____13193 with
        | (uvs,t) ->
            let attrs =
              let uu____13204 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____13204
              then
                let uu____13207 =
                  let uu____13208 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____13208
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____13207 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___411_13210 = s  in
            let uu____13211 =
              let uu____13214 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____13214  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___411_13210.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____13211;
              FStar_Syntax_Syntax.sigmeta =
                (uu___411_13210.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____13230 -> failwith "Impossible!"  in
        let c_opt =
          let uu____13236 = FStar_Syntax_Util.is_unit t  in
          if uu____13236
          then
            let uu____13241 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____13241
          else
            (let uu____13247 =
               let uu____13248 = FStar_Syntax_Subst.compress t  in
               uu____13248.FStar_Syntax_Syntax.n  in
             match uu____13247 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____13255,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____13279 -> FStar_Pervasives_Native.None)
           in
        (FStar_Option.isNone c_opt) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____13298 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____13298
           then
             let uu____13299 =
               let uu____13300 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____13300 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____13299
           else
             (let uu____13304 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____13304))
         in
      let extract_sigelt s =
        (let uu____13316 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____13316
         then
           let uu____13317 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____13317
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____13321 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____13340 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____13357 ->
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
                             (lid,uu____13401,uu____13402,uu____13403,uu____13404,uu____13405)
                             ->
                             ((let uu____13415 =
                                 let uu____13418 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____13418  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____13415);
                              (let uu____13519 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____13519 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____13523,uu____13524,uu____13525,uu____13526,uu____13527)
                             ->
                             ((let uu____13533 =
                                 let uu____13536 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____13536  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____13533);
                              sigelts1)
                         | uu____13637 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____13644 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____13644
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____13650 =
                    let uu___412_13651 = s  in
                    let uu____13652 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___412_13651.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___412_13651.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____13652;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___412_13651.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___412_13651.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____13650])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____13662 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____13662
             then []
             else
               (let uu____13666 = lbs  in
                match uu____13666 with
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
                        (fun uu____13725  ->
                           match uu____13725 with
                           | (uu____13732,t,uu____13734) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____13750  ->
                             match uu____13750 with
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
                           (fun uu____13774  ->
                              match uu____13774 with
                              | (uu____13781,t,uu____13783) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____13791,uu____13792) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____13797 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____13852 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____13852) uu____13797
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____13855 =
                    let uu___413_13856 = s  in
                    let uu____13857 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___413_13856.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___413_13856.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____13857;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___413_13856.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___413_13856.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____13855]
                else [])
             else
               (let uu____13862 =
                  let uu___414_13863 = s  in
                  let uu____13864 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___414_13863.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___414_13863.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____13864;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___414_13863.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___414_13863.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____13862])
         | FStar_Syntax_Syntax.Sig_new_effect uu____13867 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13868 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____13869 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13870 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____13883 -> [s])
         in
      let uu___415_13884 = m  in
      let uu____13885 =
        let uu____13886 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____13886 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___415_13884.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____13885;
        FStar_Syntax_Syntax.exports =
          (uu___415_13884.FStar_Syntax_Syntax.exports);
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
        (fun uu____13930  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____13969  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____13982 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____13982
  
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
      (let uu____14045 = FStar_Options.debug_any ()  in
       if uu____14045
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
         let uu___416_14050 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___416_14050.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___416_14050.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___416_14050.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___416_14050.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___416_14050.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___416_14050.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___416_14050.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___416_14050.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___416_14050.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___416_14050.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___416_14050.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___416_14050.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___416_14050.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___416_14050.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___416_14050.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___416_14050.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___416_14050.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___416_14050.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___416_14050.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___416_14050.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___416_14050.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___416_14050.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___416_14050.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___416_14050.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___416_14050.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___416_14050.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___416_14050.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___416_14050.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___416_14050.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___416_14050.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___416_14050.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___416_14050.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___416_14050.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___416_14050.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___416_14050.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___416_14050.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___416_14050.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___416_14050.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___416_14050.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____14052 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____14052 with
       | (ses,exports,env3) ->
           ((let uu___417_14085 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___417_14085.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___417_14085.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___417_14085.FStar_Syntax_Syntax.is_interface)
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
        let uu____14113 = tc_decls env decls  in
        match uu____14113 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___418_14144 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___418_14144.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___418_14144.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___418_14144.FStar_Syntax_Syntax.is_interface)
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
        let uu____14210 = tc_partial_modul env01 m  in
        match uu____14210 with
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
                (let uu____14251 = FStar_Errors.get_err_count ()  in
                 uu____14251 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____14262 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____14262
                then
                  let uu____14263 =
                    let uu____14264 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____14264 then "" else " (in lax mode) "  in
                  let uu____14266 =
                    let uu____14267 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____14267
                    then
                      let uu____14268 =
                        let uu____14269 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____14269 "\n"  in
                      Prims.strcat "\nfrom: " uu____14268
                    else ""  in
                  let uu____14271 =
                    let uu____14272 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____14272
                    then
                      let uu____14273 =
                        let uu____14274 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____14274 "\n"  in
                      Prims.strcat "\nto: " uu____14273
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____14263
                    uu____14266 uu____14271
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___419_14280 = en0  in
                    let uu____14281 =
                      let uu____14294 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____14294, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___419_14280.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___419_14280.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___419_14280.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___419_14280.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___419_14280.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___419_14280.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___419_14280.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___419_14280.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___419_14280.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___419_14280.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___419_14280.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___419_14280.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___419_14280.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___419_14280.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___419_14280.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___419_14280.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___419_14280.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___419_14280.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___419_14280.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___419_14280.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___419_14280.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___419_14280.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___419_14280.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___419_14280.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___419_14280.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___419_14280.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___419_14280.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___419_14280.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___419_14280.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___419_14280.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___419_14280.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____14281;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___419_14280.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___419_14280.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___419_14280.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___419_14280.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___419_14280.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___419_14280.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___419_14280.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___419_14280.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___419_14280.FStar_TypeChecker_Env.dep_graph)
                    }  in
                  let uu____14331 =
                    let uu____14332 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____14332  in
                  if uu____14331
                  then
                    ((let uu____14334 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____14334 (fun a238  -> ()));
                     z3_reset_options en01)
                  else en01  in
                let uu____14336 = tc_modul en0 modul_iface true  in
                match uu____14336 with
                | (modul_iface1,must_be_none,env) ->
                    if FStar_Option.isSome must_be_none
                    then
                      failwith
                        "Impossible! finish_partial_module: expected the second component to be None"
                    else
                      (((let uu___420_14380 = m  in
                         {
                           FStar_Syntax_Syntax.name =
                             (uu___420_14380.FStar_Syntax_Syntax.name);
                           FStar_Syntax_Syntax.declarations =
                             (uu___420_14380.FStar_Syntax_Syntax.declarations);
                           FStar_Syntax_Syntax.exports =
                             (modul_iface1.FStar_Syntax_Syntax.exports);
                           FStar_Syntax_Syntax.is_interface =
                             (uu___420_14380.FStar_Syntax_Syntax.is_interface)
                         })), (FStar_Pervasives_Native.Some modul_iface1),
                        env)))
            else
              (let modul =
                 let uu____14383 = FStar_Options.use_extracted_interfaces ()
                    in
                 if uu____14383
                 then
                   let uu___421_14384 = m  in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___421_14384.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations =
                       (uu___421_14384.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.exports =
                       (m.FStar_Syntax_Syntax.declarations);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___421_14384.FStar_Syntax_Syntax.is_interface)
                   }
                 else
                   (let uu___422_14386 = m  in
                    {
                      FStar_Syntax_Syntax.name =
                        (uu___422_14386.FStar_Syntax_Syntax.name);
                      FStar_Syntax_Syntax.declarations =
                        (uu___422_14386.FStar_Syntax_Syntax.declarations);
                      FStar_Syntax_Syntax.exports = exports;
                      FStar_Syntax_Syntax.is_interface =
                        (uu___422_14386.FStar_Syntax_Syntax.is_interface)
                    })
                  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____14389 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____14389 FStar_Util.smap_clear);
               (let uu____14417 =
                  ((let uu____14420 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____14420) &&
                     (let uu____14422 =
                        FStar_Options.use_extracted_interfaces ()  in
                      Prims.op_Negation uu____14422))
                    && (Prims.op_Negation loading_from_cache)
                   in
                if uu____14417 then check_exports env modul exports else ());
               (let uu____14425 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____14425 (fun a239  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____14429 =
                  let uu____14430 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____14430  in
                if uu____14429
                then
                  let uu____14431 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____14431 (fun a240  -> ())
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
        let uu____14447 =
          let uu____14448 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____14448  in
        push_context env uu____14447  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____14467 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____14478 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____14478 with | (uu____14487,uu____14488,env3) -> env3
  
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
        (let uu____14518 = FStar_Options.debug_any ()  in
         if uu____14518
         then
           let uu____14519 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____14519
         else ());
        (let uu____14523 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____14523
         then
           let uu____14524 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____14524
         else ());
        (let env1 =
           let uu___423_14527 = env  in
           let uu____14528 =
             let uu____14529 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____14529  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___423_14527.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___423_14527.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___423_14527.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___423_14527.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___423_14527.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___423_14527.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___423_14527.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___423_14527.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___423_14527.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___423_14527.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___423_14527.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___423_14527.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___423_14527.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___423_14527.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___423_14527.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___423_14527.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___423_14527.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___423_14527.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___423_14527.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___423_14527.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____14528;
             FStar_TypeChecker_Env.lax_universes =
               (uu___423_14527.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___423_14527.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___423_14527.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___423_14527.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___423_14527.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___423_14527.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___423_14527.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___423_14527.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___423_14527.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___423_14527.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___423_14527.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___423_14527.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.proof_ns =
               (uu___423_14527.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___423_14527.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___423_14527.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___423_14527.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___423_14527.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___423_14527.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___423_14527.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___423_14527.FStar_TypeChecker_Env.dep_graph)
           }  in
         let uu____14530 = tc_modul env1 m b  in
         match uu____14530 with
         | (m1,m_iface_opt,env2) ->
             ((let uu____14555 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____14555
               then
                 let uu____14556 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____14556
               else ());
              (let uu____14559 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____14559
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
                         let uu____14592 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____14592 with
                         | (univnames1,e) ->
                             let uu___424_14599 = lb  in
                             let uu____14600 =
                               let uu____14603 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____14603 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14600;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___424_14599.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___425_14604 = se  in
                       let uu____14605 =
                         let uu____14606 =
                           let uu____14613 =
                             let uu____14614 = FStar_List.map update lbs  in
                             (b1, uu____14614)  in
                           (uu____14613, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____14606  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____14605;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___425_14604.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___425_14604.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___425_14604.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___425_14604.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____14621 -> se  in
                 let normalized_module =
                   let uu___426_14623 = m1  in
                   let uu____14624 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___426_14623.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____14624;
                     FStar_Syntax_Syntax.exports =
                       (uu___426_14623.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___426_14623.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____14625 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____14625
               else ());
              (m1, m_iface_opt, env2)))
  