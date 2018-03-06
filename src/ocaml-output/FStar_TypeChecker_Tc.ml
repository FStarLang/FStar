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
          let uu___61_48 = env  in
          let uu____49 =
            let uu____62 =
              let uu____69 = let uu____74 = get_n lid  in (lid, uu____74)  in
              FStar_Pervasives_Native.Some uu____69  in
            (tbl, uu____62)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___61_48.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___61_48.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___61_48.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___61_48.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___61_48.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___61_48.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___61_48.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___61_48.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___61_48.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___61_48.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___61_48.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___61_48.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___61_48.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___61_48.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___61_48.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___61_48.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___61_48.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___61_48.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___61_48.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___61_48.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___61_48.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___61_48.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___61_48.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___61_48.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___61_48.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___61_48.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___61_48.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____49;
            FStar_TypeChecker_Env.proof_ns =
              (uu___61_48.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___61_48.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___61_48.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___61_48.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___61_48.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___61_48.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___61_48.FStar_TypeChecker_Env.dep_graph)
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
          let uu___62_98 = env  in
          let uu____99 =
            let uu____112 =
              let uu____119 = let uu____124 = get_n lid  in (lid, uu____124)
                 in
              FStar_Pervasives_Native.Some uu____119  in
            (tbl, uu____112)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___62_98.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___62_98.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___62_98.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___62_98.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___62_98.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___62_98.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___62_98.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___62_98.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___62_98.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___62_98.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___62_98.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___62_98.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___62_98.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___62_98.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___62_98.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___62_98.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___62_98.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___62_98.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___62_98.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___62_98.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___62_98.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___62_98.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___62_98.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___62_98.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___62_98.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___62_98.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___62_98.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____99;
            FStar_TypeChecker_Env.proof_ns =
              (uu___62_98.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___62_98.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___62_98.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___62_98.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___62_98.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___62_98.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___62_98.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____141 =
         let uu____142 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____142  in
       Prims.op_Negation uu____141)
  
let (user_tactics_modules : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____184 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____184 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____205 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____205
         then
           let uu____206 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____206
         else ());
        (let uu____208 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____208 with
         | (t',uu____216,uu____217) ->
             ((let uu____219 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____219
               then
                 let uu____220 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____220
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
        let uu____231 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____231
  
let check_nogen :
  'Auu____236 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____236 Prims.list,FStar_Syntax_Syntax.term)
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
        let fail uu____283 =
          let uu____284 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          FStar_Errors.raise_error uu____284 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____328)::(wp,uu____330)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____345 -> fail ())
        | uu____346 -> fail ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____353 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____353 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____379 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____379 t  in
          let open_univs_binders n_binders bs =
            let uu____389 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____389 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____397 =
            let uu____404 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____405 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____404 uu____405  in
          (match uu____397 with
           | (effect_params_un,signature_un,opening) ->
               let uu____415 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____415 with
                | (effect_params,env,uu____424) ->
                    let uu____425 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____425 with
                     | (signature,uu____431) ->
                         let ed1 =
                           let uu___63_433 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___63_433.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___63_433.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___63_433.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___63_433.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___63_433.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___63_433.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___63_433.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___63_433.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___63_433.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___63_433.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___63_433.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___63_433.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___63_433.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___63_433.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___63_433.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___63_433.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___63_433.FStar_Syntax_Syntax.actions)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____449 ->
                               let op uu____471 =
                                 match uu____471 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____491 =
                                       let uu____492 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____501 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____492
                                         uu____501
                                        in
                                     (us, uu____491)
                                  in
                               let uu___64_510 = ed1  in
                               let uu____511 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____512 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____513 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____514 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____515 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____516 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____517 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____518 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____519 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____520 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____521 =
                                 let uu____522 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____522  in
                               let uu____533 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____534 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____535 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___65_543 = a  in
                                      let uu____544 =
                                        let uu____545 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____545
                                         in
                                      let uu____554 =
                                        let uu____555 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____555
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___65_543.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___65_543.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___65_543.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___65_543.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____544;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____554
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___64_510.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___64_510.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___64_510.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___64_510.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____511;
                                 FStar_Syntax_Syntax.bind_wp = uu____512;
                                 FStar_Syntax_Syntax.if_then_else = uu____513;
                                 FStar_Syntax_Syntax.ite_wp = uu____514;
                                 FStar_Syntax_Syntax.stronger = uu____515;
                                 FStar_Syntax_Syntax.close_wp = uu____516;
                                 FStar_Syntax_Syntax.assert_p = uu____517;
                                 FStar_Syntax_Syntax.assume_p = uu____518;
                                 FStar_Syntax_Syntax.null_wp = uu____519;
                                 FStar_Syntax_Syntax.trivial = uu____520;
                                 FStar_Syntax_Syntax.repr = uu____521;
                                 FStar_Syntax_Syntax.return_repr = uu____533;
                                 FStar_Syntax_Syntax.bind_repr = uu____534;
                                 FStar_Syntax_Syntax.actions = uu____535
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____590 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____590
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____601 =
                             let uu____602 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____602.FStar_Syntax_Syntax.n  in
                           match uu____601 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____637)::(wp,uu____639)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____654 -> fail signature1)
                           | uu____655 -> fail signature1  in
                         let uu____656 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____656 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____678 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____685 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____685 with
                                     | (signature1,uu____697) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____698 ->
                                    let uu____701 =
                                      let uu____706 =
                                        let uu____707 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____707)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____706
                                       in
                                    (match uu____701 with
                                     | (uu____716,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____719 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____719
                                 in
                              ((let uu____721 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____721
                                then
                                  let uu____722 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____723 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____724 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____725 =
                                    let uu____726 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____726
                                     in
                                  let uu____727 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____722 uu____723 uu____724 uu____725
                                    uu____727
                                else ());
                               (let check_and_gen' env2 uu____743 k =
                                  match uu____743 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____757::uu____758 ->
                                           let uu____761 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____761 with
                                            | (us1,t1) ->
                                                let uu____770 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____770 with
                                                 | (us2,t2) ->
                                                     let uu____777 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____778 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____778))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____783 =
                                      let uu____790 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____791 =
                                        let uu____794 =
                                          let uu____795 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____795
                                           in
                                        [uu____794]  in
                                      uu____790 :: uu____791  in
                                    let uu____796 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____783
                                      uu____796
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____800 = fresh_effect_signature ()
                                     in
                                  match uu____800 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____816 =
                                          let uu____823 =
                                            let uu____824 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____824
                                             in
                                          [uu____823]  in
                                        let uu____825 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____816
                                          uu____825
                                         in
                                      let expected_k =
                                        let uu____831 =
                                          let uu____838 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____839 =
                                            let uu____842 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____843 =
                                              let uu____846 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____847 =
                                                let uu____850 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____851 =
                                                  let uu____854 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____854]  in
                                                uu____850 :: uu____851  in
                                              uu____846 :: uu____847  in
                                            uu____842 :: uu____843  in
                                          uu____838 :: uu____839  in
                                        let uu____855 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____831
                                          uu____855
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____860 =
                                      let uu____861 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____861
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____860
                                     in
                                  let expected_k =
                                    let uu____873 =
                                      let uu____880 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____881 =
                                        let uu____884 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____885 =
                                          let uu____888 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____889 =
                                            let uu____892 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____892]  in
                                          uu____888 :: uu____889  in
                                        uu____884 :: uu____885  in
                                      uu____880 :: uu____881  in
                                    let uu____893 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____873
                                      uu____893
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____900 =
                                      let uu____907 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____908 =
                                        let uu____911 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____911]  in
                                      uu____907 :: uu____908  in
                                    let uu____912 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____900
                                      uu____912
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____916 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____916 with
                                  | (t,uu____922) ->
                                      let expected_k =
                                        let uu____926 =
                                          let uu____933 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____934 =
                                            let uu____937 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____938 =
                                              let uu____941 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____941]  in
                                            uu____937 :: uu____938  in
                                          uu____933 :: uu____934  in
                                        let uu____942 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____926
                                          uu____942
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____947 =
                                      let uu____948 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____948
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____947
                                     in
                                  let b_wp_a =
                                    let uu____960 =
                                      let uu____967 =
                                        let uu____968 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____968
                                         in
                                      [uu____967]  in
                                    let uu____969 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____960
                                      uu____969
                                     in
                                  let expected_k =
                                    let uu____975 =
                                      let uu____982 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____983 =
                                        let uu____986 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____987 =
                                          let uu____990 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____990]  in
                                        uu____986 :: uu____987  in
                                      uu____982 :: uu____983  in
                                    let uu____991 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____975
                                      uu____991
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____998 =
                                      let uu____1005 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1006 =
                                        let uu____1009 =
                                          let uu____1010 =
                                            let uu____1011 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1011
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1010
                                           in
                                        let uu____1020 =
                                          let uu____1023 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1023]  in
                                        uu____1009 :: uu____1020  in
                                      uu____1005 :: uu____1006  in
                                    let uu____1024 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____998
                                      uu____1024
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1031 =
                                      let uu____1038 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1039 =
                                        let uu____1042 =
                                          let uu____1043 =
                                            let uu____1044 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1044
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1043
                                           in
                                        let uu____1053 =
                                          let uu____1056 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1056]  in
                                        uu____1042 :: uu____1053  in
                                      uu____1038 :: uu____1039  in
                                    let uu____1057 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1031
                                      uu____1057
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1064 =
                                      let uu____1071 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1071]  in
                                    let uu____1072 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1064
                                      uu____1072
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1076 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1076 with
                                  | (t,uu____1082) ->
                                      let expected_k =
                                        let uu____1086 =
                                          let uu____1093 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1094 =
                                            let uu____1097 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1097]  in
                                          uu____1093 :: uu____1094  in
                                        let uu____1098 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1086
                                          uu____1098
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1101 =
                                  let uu____1112 =
                                    let uu____1113 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1113.FStar_Syntax_Syntax.n  in
                                  match uu____1112 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1128 ->
                                      let repr =
                                        let uu____1130 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1130 with
                                        | (t,uu____1136) ->
                                            let expected_k =
                                              let uu____1140 =
                                                let uu____1147 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1148 =
                                                  let uu____1151 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1151]  in
                                                uu____1147 :: uu____1148  in
                                              let uu____1152 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1140 uu____1152
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
                                        let uu____1165 =
                                          let uu____1168 =
                                            let uu____1169 =
                                              let uu____1184 =
                                                let uu____1187 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1188 =
                                                  let uu____1191 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1191]  in
                                                uu____1187 :: uu____1188  in
                                              (repr1, uu____1184)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1169
                                             in
                                          FStar_Syntax_Syntax.mk uu____1168
                                           in
                                        uu____1165
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1206 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1206 wp  in
                                      let destruct_repr t =
                                        let uu____1219 =
                                          let uu____1220 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1220.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1219 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1231,(t1,uu____1233)::
                                             (wp,uu____1235)::[])
                                            -> (t1, wp)
                                        | uu____1278 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1289 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1289
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1290 =
                                          fresh_effect_signature ()  in
                                        match uu____1290 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1306 =
                                                let uu____1313 =
                                                  let uu____1314 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1314
                                                   in
                                                [uu____1313]  in
                                              let uu____1315 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1306 uu____1315
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
                                              let uu____1321 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1321
                                               in
                                            let wp_g_x =
                                              let uu____1325 =
                                                let uu____1326 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1327 =
                                                  let uu____1328 =
                                                    let uu____1329 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1329
                                                     in
                                                  [uu____1328]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1326 uu____1327
                                                 in
                                              uu____1325
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1338 =
                                                  let uu____1339 =
                                                    let uu____1340 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1340
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1349 =
                                                    let uu____1350 =
                                                      let uu____1353 =
                                                        let uu____1356 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1357 =
                                                          let uu____1360 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1361 =
                                                            let uu____1364 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1365 =
                                                              let uu____1368
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1368]
                                                               in
                                                            uu____1364 ::
                                                              uu____1365
                                                             in
                                                          uu____1360 ::
                                                            uu____1361
                                                           in
                                                        uu____1356 ::
                                                          uu____1357
                                                         in
                                                      r :: uu____1353  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1350
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1339 uu____1349
                                                   in
                                                uu____1338
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let expected_k =
                                              let uu____1374 =
                                                let uu____1381 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1382 =
                                                  let uu____1385 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____1386 =
                                                    let uu____1389 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1390 =
                                                      let uu____1393 =
                                                        let uu____1394 =
                                                          let uu____1395 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1395
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1394
                                                         in
                                                      let uu____1396 =
                                                        let uu____1399 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1400 =
                                                          let uu____1403 =
                                                            let uu____1404 =
                                                              let uu____1405
                                                                =
                                                                let uu____1412
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1412]
                                                                 in
                                                              let uu____1413
                                                                =
                                                                let uu____1416
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1416
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1405
                                                                uu____1413
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1404
                                                             in
                                                          [uu____1403]  in
                                                        uu____1399 ::
                                                          uu____1400
                                                         in
                                                      uu____1393 ::
                                                        uu____1396
                                                       in
                                                    uu____1389 :: uu____1390
                                                     in
                                                  uu____1385 :: uu____1386
                                                   in
                                                uu____1381 :: uu____1382  in
                                              let uu____1417 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1374 uu____1417
                                               in
                                            let uu____1420 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1420 with
                                             | (expected_k1,uu____1428,uu____1429)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___66_1434 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___66_1434.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1444 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1444
                                           in
                                        let res =
                                          let wp =
                                            let uu____1451 =
                                              let uu____1452 =
                                                let uu____1453 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1453
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1462 =
                                                let uu____1463 =
                                                  let uu____1466 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1467 =
                                                    let uu____1470 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1470]  in
                                                  uu____1466 :: uu____1467
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1463
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1452 uu____1462
                                               in
                                            uu____1451
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1476 =
                                            let uu____1483 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1484 =
                                              let uu____1487 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1487]  in
                                            uu____1483 :: uu____1484  in
                                          let uu____1488 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1476
                                            uu____1488
                                           in
                                        let uu____1491 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1491 with
                                        | (expected_k1,uu____1505,uu____1506)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1510 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1510 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1531 ->
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
                                              (let uu____1558 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____1558 with
                                               | (usubst,uvs) ->
                                                   let uu___67_1577 = act  in
                                                   let uu____1578 =
                                                     FStar_Syntax_Subst.subst_binders
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_params
                                                      in
                                                   let uu____1579 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_defn
                                                      in
                                                   let uu____1580 =
                                                     FStar_Syntax_Subst.subst
                                                       usubst
                                                       act.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___67_1577.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___67_1577.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.action_params
                                                       = uu____1578;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____1579;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____1580
                                                   })
                                             in
                                          let act_typ =
                                            let uu____1584 =
                                              let uu____1585 =
                                                FStar_Syntax_Subst.compress
                                                  act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              uu____1585.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1584 with
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
                                                  let uu____1611 =
                                                    let uu____1614 =
                                                      let uu____1615 =
                                                        let uu____1616 =
                                                          FStar_List.hd
                                                            c1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        FStar_Pervasives_Native.fst
                                                          uu____1616
                                                         in
                                                      mk_repr'
                                                        c1.FStar_Syntax_Syntax.result_typ
                                                        uu____1615
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total
                                                      uu____1614
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____1611
                                                else
                                                  act1.FStar_Syntax_Syntax.action_typ
                                            | uu____1632 ->
                                                act1.FStar_Syntax_Syntax.action_typ
                                             in
                                          let uu____1633 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1 act_typ
                                             in
                                          match uu____1633 with
                                          | (act_typ1,uu____1641,g_t) ->
                                              let env' =
                                                let uu___68_1644 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ1
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___68_1644.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___68_1644.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1646 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1646
                                                then
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
                                                    (FStar_Ident.text_of_lid
                                                       act1.FStar_Syntax_Syntax.action_name)
                                                    uu____1647 uu____1648
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
                                                               let uu___69_1829
                                                                 = act1  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___69_1829.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___69_1829.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___69_1829.FStar_Syntax_Syntax.action_params);
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
                                match uu____1101 with
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
                                                           (FStar_Syntax_Syntax.order_univ_name
                                                              u1 u2)
                                                             =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names)
                                                  in
                                               if uu____1887
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1901 =
                                                    let uu____1906 =
                                                      let uu____1907 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1908 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1907 uu____1908
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1906)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1901
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1856 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1922 =
                                             let uu____1927 =
                                               let uu____1928 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1928.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1927)  in
                                           match uu____1922 with
                                           | ([],uu____1931) -> t
                                           | (uu____1942,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1943,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1961 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1974 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1974
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1979 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1981 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1981))
                                                && (m <> n1)
                                               in
                                            if uu____1979
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1997 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2004 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2005 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1997 uu____2004
                                                  uu____2005
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2013 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2013 with
                                           | (univs2,defn) ->
                                               let uu____2020 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2020 with
                                                | (univs',typ) ->
                                                    let uu___70_2030 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___70_2030.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___70_2030.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___70_2030.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___71_2035 = ed2  in
                                           let uu____2036 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____2037 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____2038 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____2039 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____2040 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____2041 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____2042 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____2043 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____2044 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____2045 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____2046 =
                                             let uu____2047 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2047
                                              in
                                           let uu____2058 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____2059 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2060 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___71_2035.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___71_2035.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2036;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2037;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2038;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2039;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2040;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2041;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2042;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2043;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2044;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2045;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2046;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2058;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2059;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2060
                                           }  in
                                         ((let uu____2064 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2064
                                           then
                                             let uu____2065 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2065
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
      let uu____2083 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2083 with
      | (effect_binders_un,signature_un) ->
          let uu____2100 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2100 with
           | (effect_binders,env1,uu____2119) ->
               let uu____2120 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2120 with
                | (signature,uu____2136) ->
                    let raise_error1 a uu____2147 =
                      match uu____2147 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2173  ->
                           match uu____2173 with
                           | (bv,qual) ->
                               let uu____2184 =
                                 let uu___72_2185 = bv  in
                                 let uu____2186 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___72_2185.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___72_2185.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2186
                                 }  in
                               (uu____2184, qual)) effect_binders
                       in
                    let uu____2189 =
                      let uu____2196 =
                        let uu____2197 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2197.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2196 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2207)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2229 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2189 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2247 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2247
                           then
                             let uu____2248 =
                               let uu____2251 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2251  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2248
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2285 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2285 with
                           | (t2,comp,uu____2298) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2305 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2305 with
                          | (repr,_comp) ->
                              ((let uu____2327 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2327
                                then
                                  let uu____2328 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2328
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
                                  let uu____2334 =
                                    let uu____2335 =
                                      let uu____2336 =
                                        let uu____2351 =
                                          let uu____2358 =
                                            let uu____2363 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2364 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2363, uu____2364)  in
                                          [uu____2358]  in
                                        (wp_type1, uu____2351)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2336
                                       in
                                    mk1 uu____2335  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2334
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2389 =
                                      let uu____2394 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2394)  in
                                    let uu____2395 =
                                      let uu____2402 =
                                        let uu____2403 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2403
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2402]  in
                                    uu____2389 :: uu____2395  in
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
                                  let uu____2466 = item  in
                                  match uu____2466 with
                                  | (u_item,item1) ->
                                      let uu____2487 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2487 with
                                       | (item2,item_comp) ->
                                           ((let uu____2503 =
                                               let uu____2504 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2504
                                                in
                                             if uu____2503
                                             then
                                               let uu____2505 =
                                                 let uu____2510 =
                                                   let uu____2511 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2512 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2511 uu____2512
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2510)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2505
                                             else ());
                                            (let uu____2514 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2514 with
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
                                let uu____2534 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2534 with
                                | (dmff_env1,uu____2558,bind_wp,bind_elab) ->
                                    let uu____2561 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2561 with
                                     | (dmff_env2,uu____2585,return_wp,return_elab)
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
                                           let uu____2592 =
                                             let uu____2593 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2593.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2592 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2637 =
                                                       let uu____2652 =
                                                         let uu____2657 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2657
                                                          in
                                                       match uu____2652 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2721 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2637 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2760 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2760
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2777 =
                                                               let uu____2778
                                                                 =
                                                                 let uu____2793
                                                                   =
                                                                   let uu____2800
                                                                    =
                                                                    let uu____2805
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2806
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2805,
                                                                    uu____2806)
                                                                     in
                                                                   [uu____2800]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2793)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2778
                                                                in
                                                             mk1 uu____2777
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2821 =
                                                           let uu____2830 =
                                                             let uu____2831 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2831
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2830
                                                            in
                                                         (match uu____2821
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a413 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2850
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2852
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2852
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
                                                                  a413
                                                                 in
                                                              ((match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                    then
                                                                    fail ()
                                                                    else ();
                                                                    (
                                                                    let uu____2858
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
                                                                    fail ())
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2858
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
                                                                  let uu____2885
                                                                    =
                                                                    let uu____2886
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2887
                                                                    =
                                                                    let uu____2888
                                                                    =
                                                                    let uu____2895
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2895,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2888]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2886
                                                                    uu____2887
                                                                     in
                                                                  uu____2885
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2920
                                                                  =
                                                                  let uu____2921
                                                                    =
                                                                    let uu____2928
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2928]
                                                                     in
                                                                  b11 ::
                                                                    uu____2921
                                                                   in
                                                                let uu____2933
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2920
                                                                  uu____2933
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2934 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2936 =
                                             let uu____2937 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2937.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2936 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2981 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2981
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2994 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2996 =
                                             let uu____2997 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2997.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2996 with
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
                                                     let uu____3024 =
                                                       let uu____3025 =
                                                         let uu____3028 =
                                                           let uu____3029 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3029
                                                            in
                                                         [uu____3028]  in
                                                       FStar_List.append
                                                         uu____3025 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____3024 body what)
                                              | uu____3030 ->
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
                                             (let uu____3048 =
                                                let uu____3049 =
                                                  let uu____3050 =
                                                    let uu____3065 =
                                                      let uu____3066 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3066
                                                       in
                                                    (t, uu____3065)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3050
                                                   in
                                                mk1 uu____3049  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3048)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3096 = f a2  in
                                               [uu____3096]
                                           | x::xs ->
                                               let uu____3101 =
                                                 apply_last1 f xs  in
                                               x :: uu____3101
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
                                           let uu____3121 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3121 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3151 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3151
                                                 then
                                                   let uu____3152 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3152
                                                 else ());
                                                (let uu____3154 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3154))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3163 =
                                                 let uu____3168 = mk_lid name
                                                    in
                                                 let uu____3169 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3168 uu____3169
                                                  in
                                               (match uu____3163 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3173 =
                                                        let uu____3176 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3176
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3173);
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
                                          (let uu____3273 =
                                             let uu____3276 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3277 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3276 :: uu____3277  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3273);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3375 =
                                               let uu____3378 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3379 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3378 :: uu____3379  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3375);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3474 =
                                                FStar_List.fold_left
                                                  (fun uu____3514  ->
                                                     fun action  ->
                                                       match uu____3514 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3535 =
                                                             let uu____3542 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3542
                                                               params_un
                                                              in
                                                           (match uu____3535
                                                            with
                                                            | (action_params,env',uu____3551)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3571
                                                                     ->
                                                                    match uu____3571
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3582
                                                                    =
                                                                    let uu___73_3583
                                                                    = bv  in
                                                                    let uu____3584
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___73_3583.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___73_3583.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3584
                                                                    }  in
                                                                    (uu____3582,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3588
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3588
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
                                                                    uu____3618
                                                                    ->
                                                                    let uu____3619
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3619
                                                                     in
                                                                    ((
                                                                    let uu____3623
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3623
                                                                    then
                                                                    let uu____3624
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3625
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3626
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3627
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3624
                                                                    uu____3625
                                                                    uu____3626
                                                                    uu____3627
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
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu___74_3635
                                                                    = action
                                                                     in
                                                                    let uu____3636
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3637
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___74_3635.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___74_3635.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___74_3635.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3636;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3637
                                                                    }  in
                                                                    uu____3634
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3631))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3474 with
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
                                                      let uu____3670 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3671 =
                                                        let uu____3674 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3674]  in
                                                      uu____3670 ::
                                                        uu____3671
                                                       in
                                                    let uu____3675 =
                                                      let uu____3676 =
                                                        let uu____3677 =
                                                          let uu____3678 =
                                                            let uu____3693 =
                                                              let uu____3700
                                                                =
                                                                let uu____3705
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3706
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3705,
                                                                  uu____3706)
                                                                 in
                                                              [uu____3700]
                                                               in
                                                            (repr,
                                                              uu____3693)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3678
                                                           in
                                                        mk1 uu____3677  in
                                                      let uu____3721 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3676
                                                        uu____3721
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3675
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3724 =
                                                    let uu____3731 =
                                                      let uu____3732 =
                                                        let uu____3735 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3735
                                                         in
                                                      uu____3732.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3731 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3745)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3774
                                                                =
                                                                let uu____3791
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3791
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3849
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3774
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3899
                                                                    =
                                                                    let uu____3900
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3903
                                                                     in
                                                                    uu____3900.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3899
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3928
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3928
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3941
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3966
                                                                     ->
                                                                    match uu____3966
                                                                    with
                                                                    | 
                                                                    (bv,uu____3972)
                                                                    ->
                                                                    let uu____3973
                                                                    =
                                                                    let uu____3974
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3974
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3973
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3941
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
                                                                    let uu____4038
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4038
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4043
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4051
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4051
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4056
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4059
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4056,
                                                                    uu____4059)))
                                                                    | 
                                                                    uu____4066
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4067
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4073
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4073
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4072)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4067)))
                                                       | uu____4074 ->
                                                           Obj.repr
                                                             (let uu____4075
                                                                =
                                                                let uu____4080
                                                                  =
                                                                  let uu____4081
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4081
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4080)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4075))
                                                     in
                                                  (match uu____3724 with
                                                   | (pre,post) ->
                                                       ((let uu____4099 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4101 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4103 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___75_4105 =
                                                             ed  in
                                                           let uu____4106 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4107 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4108 =
                                                             let uu____4109 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4109)
                                                              in
                                                           let uu____4116 =
                                                             let uu____4117 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4117)
                                                              in
                                                           let uu____4124 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4125 =
                                                             let uu____4126 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4126)
                                                              in
                                                           let uu____4133 =
                                                             let uu____4134 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4134)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4106;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4107;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4108;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4116;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___75_4105.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4124;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4125;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4133;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____4141 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4141
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4159
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4159
                                                               then
                                                                 let uu____4160
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4160
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
                                                                    let uu____4172
                                                                    =
                                                                    let uu____4175
                                                                    =
                                                                    let uu____4184
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4184)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4175
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
                                                                    uu____4172;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4199
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4199
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4201
                                                                 =
                                                                 let uu____4204
                                                                   =
                                                                   let uu____4207
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4207
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4204
                                                                   sigelts'
                                                                  in
                                                               (uu____4201,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4264 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4264 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4297 = FStar_List.hd ses  in
            uu____4297.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4302 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4306,[],t,uu____4308,uu____4309);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4311;
               FStar_Syntax_Syntax.sigattrs = uu____4312;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4314,_t_top,_lex_t_top,_0_40,uu____4317);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4319;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4320;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4322,_t_cons,_lex_t_cons,_0_41,uu____4325);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4327;
                 FStar_Syntax_Syntax.sigattrs = uu____4328;_}::[]
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
                 let uu____4387 =
                   let uu____4390 =
                     let uu____4391 =
                       let uu____4398 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4398, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4391  in
                   FStar_Syntax_Syntax.mk uu____4390  in
                 uu____4387 FStar_Pervasives_Native.None r1  in
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
                   let uu____4416 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4416
                    in
                 let hd1 =
                   let uu____4418 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4418
                    in
                 let tl1 =
                   let uu____4420 =
                     let uu____4421 =
                       let uu____4424 =
                         let uu____4425 =
                           let uu____4432 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4432, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4425  in
                       FStar_Syntax_Syntax.mk uu____4424  in
                     uu____4421 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4420
                    in
                 let res =
                   let uu____4441 =
                     let uu____4444 =
                       let uu____4445 =
                         let uu____4452 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4452,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4445  in
                     FStar_Syntax_Syntax.mk uu____4444  in
                   uu____4441 FStar_Pervasives_Native.None r2  in
                 let uu____4458 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4458
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
               let uu____4497 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4497;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4502 ->
               let err_msg =
                 let uu____4506 =
                   let uu____4507 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4507  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4506
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
            let uu____4532 = FStar_Syntax_Util.type_u ()  in
            match uu____4532 with
            | (k,uu____4538) ->
                let phi1 =
                  let uu____4540 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4540
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4542 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4542 with
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
          let uu____4584 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4584 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4617 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4617 FStar_List.flatten  in
              ((let uu____4631 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4631
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
                          let uu____4642 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4652,uu____4653,uu____4654,uu____4655,uu____4656)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4665 -> failwith "Impossible!"  in
                          match uu____4642 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4676 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4680,uu____4681,uu____4682,uu____4683,uu____4684)
                        -> lid
                    | uu____4693 -> failwith "Impossible"  in
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
                  let uu____4711 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4711
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
                     let uu____4734 =
                       let uu____4737 =
                         let uu____4738 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4738;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4737 :: ses1  in
                     (uu____4734, data_ops_ses))
                   in
                (let uu____4748 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive"  in
                 ());
                res))
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4782 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4807 ->
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
           let uu____4859 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4859 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4897 = cps_and_elaborate env1 ne  in
           (match uu____4897 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___76_4934 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4934.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4934.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4934.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4934.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___77_4936 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___77_4936.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___77_4936.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___77_4936.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___77_4936.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___78_4944 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___78_4944.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___78_4944.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___78_4944.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___78_4944.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4952 =
             let uu____4959 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4959
              in
           (match uu____4952 with
            | (a,wp_a_src) ->
                let uu____4974 =
                  let uu____4981 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4981
                   in
                (match uu____4974 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4997 =
                         let uu____5000 =
                           let uu____5001 =
                             let uu____5008 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5008)  in
                           FStar_Syntax_Syntax.NT uu____5001  in
                         [uu____5000]  in
                       FStar_Syntax_Subst.subst uu____4997 wp_b_tgt  in
                     let expected_k =
                       let uu____5012 =
                         let uu____5019 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5020 =
                           let uu____5023 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5023]  in
                         uu____5019 :: uu____5020  in
                       let uu____5024 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5012 uu____5024  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5045 =
                           let uu____5050 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5050)
                            in
                         let uu____5051 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5045 uu____5051  in
                       let uu____5054 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5054 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5086 =
                             let uu____5087 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5087  in
                           if uu____5086
                           then no_reify eff_name
                           else
                             (let uu____5093 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5094 =
                                let uu____5097 =
                                  let uu____5098 =
                                    let uu____5113 =
                                      let uu____5116 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5117 =
                                        let uu____5120 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5120]  in
                                      uu____5116 :: uu____5117  in
                                    (repr, uu____5113)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5098  in
                                FStar_Syntax_Syntax.mk uu____5097  in
                              uu____5094 FStar_Pervasives_Native.None
                                uu____5093)
                        in
                     let uu____5126 =
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
                               let uu____5179 =
                                 let uu____5182 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5182  in
                               FStar_Syntax_Subst.subst uu____5179 lift_wp
                             else lift_wp  in
                           let uu____5196 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5196)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5222 =
                                 let uu____5225 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5225  in
                               FStar_Syntax_Subst.subst uu____5222 lift
                             else lift  in
                           ((let uu____5240 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5240
                             then
                               let uu____5241 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5241
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5244 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5244 with
                             | (lift2,comp,uu____5259) ->
                                 let uu____5260 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5260 with
                                  | (uu____5273,lift_wp,lift_elab) ->
                                      let uu____5276 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5277 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5126 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___79_5318 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___79_5318.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___79_5318.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___79_5318.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___79_5318.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___79_5318.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___79_5318.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___79_5318.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___79_5318.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___79_5318.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___79_5318.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___79_5318.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___79_5318.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___79_5318.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___79_5318.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___79_5318.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___79_5318.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___79_5318.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___79_5318.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___79_5318.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___79_5318.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___79_5318.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___79_5318.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___79_5318.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___79_5318.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___79_5318.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___79_5318.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___79_5318.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___79_5318.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___79_5318.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___79_5318.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___79_5318.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___79_5318.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___79_5318.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___79_5318.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let lift2 =
                                  let uu____5337 =
                                    let uu____5340 =
                                      FStar_Syntax_Subst.univ_var_opening uvs
                                       in
                                    FStar_Pervasives_Native.fst uu____5340
                                     in
                                  FStar_Syntax_Subst.subst uu____5337 lift1
                                   in
                                let uu____5353 =
                                  let uu____5360 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5360
                                   in
                                (match uu____5353 with
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
                                         let uu____5384 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5385 =
                                           let uu____5388 =
                                             let uu____5389 =
                                               let uu____5404 =
                                                 let uu____5407 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5408 =
                                                   let uu____5411 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5411]  in
                                                 uu____5407 :: uu____5408  in
                                               (lift_wp1, uu____5404)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5389
                                              in
                                           FStar_Syntax_Syntax.mk uu____5388
                                            in
                                         uu____5385
                                           FStar_Pervasives_Native.None
                                           uu____5384
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5420 =
                                         let uu____5427 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5428 =
                                           let uu____5431 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5432 =
                                             let uu____5435 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5435]  in
                                           uu____5431 :: uu____5432  in
                                         uu____5427 :: uu____5428  in
                                       let uu____5436 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5420
                                         uu____5436
                                        in
                                     let uu____5439 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5439 with
                                      | (expected_k2,uu____5449,uu____5450)
                                          ->
                                          let lift3 =
                                            check_and_gen env2 lift2
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift3))
                             in
                          let sub2 =
                            let uu___80_5453 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___80_5453.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___80_5453.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___81_5455 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___81_5455.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___81_5455.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___81_5455.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___81_5455.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5470 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5484 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5484 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5511 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5511 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5470 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5532 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5532 with
                 | (tps2,c2) ->
                     let uu____5547 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5547 with
                      | (tps3,env3,us) ->
                          let uu____5565 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5565 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5586 =
                                   let uu____5587 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5587
                                    in
                                 match uu____5586 with
                                 | (uvs2,t) ->
                                     let uu____5602 =
                                       let uu____5615 =
                                         let uu____5620 =
                                           let uu____5621 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5621.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5620)  in
                                       match uu____5615 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5636,c5)) -> ([], c5)
                                       | (uu____5676,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5703 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5602 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5747 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5747 with
                                              | (uu____5752,t1) ->
                                                  let uu____5754 =
                                                    let uu____5759 =
                                                      let uu____5760 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5761 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5762 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5760 uu____5761
                                                        uu____5762
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5759)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5754 r)
                                           else ();
                                           (let se1 =
                                              let uu___82_5765 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___82_5765.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___82_5765.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___82_5765.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___82_5765.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5782,uu____5783,uu____5784) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5788  ->
                   match uu___56_5788 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5789 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5794,uu____5795) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5803  ->
                   match uu___56_5803 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5804 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5814 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5814
             then
               let uu____5815 =
                 let uu____5820 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5820)
                  in
               FStar_Errors.raise_error uu____5815 r
             else ());
            (let uu____5822 =
               if uvs = []
               then
                 let uu____5823 =
                   let uu____5824 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5824  in
                 check_and_gen env2 t uu____5823
               else
                 (let uu____5830 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5830 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5838 =
                          let uu____5839 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5839  in
                        tc_check_trivial_guard env2 t1 uu____5838  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5845 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5845))
                in
             match uu____5822 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___83_5861 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___83_5861.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___83_5861.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___83_5861.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___83_5861.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5871 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5871 with
            | (uu____5884,phi1) ->
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
           let uu____5894 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5894 with
            | (e1,c,g1) ->
                let uu____5912 =
                  let uu____5919 =
                    let uu____5922 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5922  in
                  let uu____5923 =
                    let uu____5928 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5928)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5919 uu____5923
                   in
                (match uu____5912 with
                 | (e2,uu____5938,g) ->
                     ((let uu____5941 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5941);
                      (let se1 =
                         let uu___84_5943 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___84_5943.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___84_5943.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___84_5943.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___84_5943.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5994 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5994
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6002 =
                      let uu____6007 =
                        let uu____6008 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6009 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6010 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6008 uu____6009 uu____6010
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6007)
                       in
                    FStar_Errors.raise_error uu____6002 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6036 =
                   let uu____6037 = FStar_Syntax_Subst.compress def  in
                   uu____6037.FStar_Syntax_Syntax.n  in
                 match uu____6036 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6047,uu____6048)
                     -> binders
                 | uu____6069 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6079;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6157) -> val_bs1
                     | (uu____6180,[]) -> val_bs1
                     | ((body_bv,uu____6204)::bt,(val_bv,aqual)::vt) ->
                         let uu____6241 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6257) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___85_6259 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___86_6262 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___86_6262.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___85_6259.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___85_6259.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6241
                      in
                   let uu____6263 =
                     let uu____6266 =
                       let uu____6267 =
                         let uu____6280 = rename_binders1 def_bs val_bs  in
                         (uu____6280, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6267  in
                     FStar_Syntax_Syntax.mk uu____6266  in
                   uu____6263 FStar_Pervasives_Native.None r1
               | uu____6298 -> typ1  in
             let uu___87_6299 = lb  in
             let uu____6300 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___87_6299.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___87_6299.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6300;
               FStar_Syntax_Syntax.lbeff =
                 (uu___87_6299.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___87_6299.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___87_6299.FStar_Syntax_Syntax.lbattrs)
             }  in
           let uu____6303 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6354  ->
                     fun lb  ->
                       match uu____6354 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6396 =
                             let uu____6407 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6407 with
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
                                   | uu____6492 ->
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
                                  (let uu____6535 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6535, quals_opt1)))
                              in
                           (match uu____6396 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6303 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6629 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6633  ->
                                match uu___57_6633 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6634 -> false))
                         in
                      if uu____6629
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6644 =
                    let uu____6647 =
                      let uu____6648 =
                        let uu____6661 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6661)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6648  in
                    FStar_Syntax_Syntax.mk uu____6647  in
                  uu____6644 FStar_Pervasives_Native.None r  in
                let uu____6679 =
                  let uu____6690 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___88_6699 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___88_6699.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___88_6699.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___88_6699.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___88_6699.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___88_6699.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___88_6699.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___88_6699.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___88_6699.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___88_6699.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___88_6699.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___88_6699.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___88_6699.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___88_6699.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___88_6699.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___88_6699.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___88_6699.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___88_6699.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___88_6699.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___88_6699.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___88_6699.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___88_6699.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___88_6699.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___88_6699.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___88_6699.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___88_6699.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___88_6699.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___88_6699.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___88_6699.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___88_6699.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___88_6699.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___88_6699.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___88_6699.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___88_6699.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6690 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6712;
                       FStar_Syntax_Syntax.vars = uu____6713;_},uu____6714,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6743 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6743)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6761,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6766 -> quals  in
                      ((let uu___89_6774 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___89_6774.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___89_6774.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___89_6774.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6783 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6679 with
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
                      (let uu____6832 = log env2  in
                       if uu____6832
                       then
                         let uu____6833 =
                           let uu____6834 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6849 =
                                         let uu____6858 =
                                           let uu____6859 =
                                             let uu____6862 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6862.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6859.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6858
                                          in
                                       match uu____6849 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6869 -> false  in
                                     if should_log
                                     then
                                       let uu____6878 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6879 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6878 uu____6879
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6834
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6833
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6910 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____6910 with
                              | (bs1,c1) ->
                                  let uu____6917 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____6917
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6929 =
                                            let uu____6930 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____6930.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6929 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6955 =
                                                 let uu____6956 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____6956.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6955 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6966 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6966
                                                       in
                                                    let uu____6967 =
                                                      let uu____6968 =
                                                        let uu____6969 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6969 args
                                                         in
                                                      uu____6968
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6967 u
                                                | uu____6972 -> c1)
                                           | uu____6973 -> c1)
                                      | uu____6974 -> c1  in
                                    let uu___90_6975 = t1  in
                                    let uu____6976 =
                                      let uu____6977 =
                                        let uu____6990 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____6990)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6977
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6976;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___90_6975.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___90_6975.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____7014 =
                               let uu____7015 = FStar_Syntax_Subst.compress h
                                  in
                               uu____7015.FStar_Syntax_Syntax.n  in
                             (match uu____7014 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____7025 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____7025
                                     in
                                  let uu____7026 =
                                    let uu____7027 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7027
                                      args
                                     in
                                  uu____7026 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____7030 -> t1)
                         | uu____7031 -> t1  in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (assm_lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                  t));
                           FStar_Syntax_Syntax.sigrng =
                             (FStar_Ident.range_of_lid assm_lid);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____7059 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____7059
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____7076 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x)
                                   in
                                (uu____7076, (FStar_Pervasives_Native.snd x)))
                             bs
                            in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.effect_TAC_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let body =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let uu___91_7109 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___92_7121 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___92_7121.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___92_7121.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___92_7121.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___92_7121.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___92_7121.FStar_Syntax_Syntax.lbattrs)
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___91_7109.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___91_7109.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___91_7109.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___91_7109.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7138 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____7138 with
                              | (bs,comp) ->
                                  if
                                    (FStar_Ident.lid_equals
                                       FStar_Parser_Const.effect_Tac_lid
                                       (FStar_Syntax_Util.comp_effect_name
                                          comp))
                                      ||
                                      (FStar_Ident.lid_equals
                                         FStar_Parser_Const.effect_TAC_lid
                                         (FStar_Syntax_Util.comp_effect_name
                                            comp))
                                  then
                                    let t =
                                      FStar_Syntax_Util.comp_result comp  in
                                    let tac_lid =
                                      let uu____7179 =
                                        let uu____7182 =
                                          FStar_Util.right
                                            hd1.FStar_Syntax_Syntax.lbname
                                           in
                                        uu____7182.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____7179.FStar_Syntax_Syntax.v  in
                                    let assm_lid =
                                      let uu____7184 =
                                        FStar_All.pipe_left
                                          FStar_Ident.id_of_text
                                          (Prims.strcat "__"
                                             (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                         in
                                      FStar_Ident.lid_of_ns_and_id
                                        tac_lid.FStar_Ident.ns uu____7184
                                       in
                                    let uu____7185 =
                                      let uu____7186 =
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env2 tac_lid
                                         in
                                      FStar_All.pipe_left FStar_Util.is_some
                                        uu____7186
                                       in
                                    (if uu____7185
                                     then FStar_Pervasives_Native.None
                                     else
                                       ((let uu____7221 =
                                           let uu____7222 =
                                             FStar_Syntax_Util.is_builtin_tactic
                                               env2.FStar_TypeChecker_Env.curmodule
                                              in
                                           Prims.op_Negation uu____7222  in
                                         if uu____7221
                                         then
                                           let added_modules =
                                             FStar_ST.op_Bang
                                               user_tactics_modules
                                              in
                                           let module_name =
                                             FStar_Ident.ml_path_of_lid
                                               env2.FStar_TypeChecker_Env.curmodule
                                              in
                                           (if
                                              Prims.op_Negation
                                                (FStar_List.contains
                                                   module_name added_modules)
                                            then
                                              FStar_ST.op_Colon_Equals
                                                user_tactics_modules
                                                (FStar_List.append
                                                   added_modules
                                                   [module_name])
                                            else ())
                                         else ());
                                        (let uu____7275 =
                                           env2.FStar_TypeChecker_Env.is_native_tactic
                                             assm_lid
                                            in
                                         if uu____7275
                                         then
                                           let se_assm =
                                             reified_tactic_decl assm_lid hd1
                                              in
                                           let se_refl =
                                             reflected_tactic_decl
                                               (FStar_Pervasives_Native.fst
                                                  lbs1) hd1 bs assm_lid comp
                                              in
                                           FStar_Pervasives_Native.Some
                                             (se_assm, se_refl)
                                         else FStar_Pervasives_Native.None)))
                                  else FStar_Pervasives_Native.None)
                         | uu____7300 -> FStar_Pervasives_Native.None  in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7322 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____7322
                             then
                               let uu____7323 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____7324 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7323 uu____7324
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
  
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
             (fun uu___58_7375  ->
                match uu___58_7375 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7376 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7382) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7388 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7397 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7402 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7427 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7451) ->
          let uu____7460 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7460
          then
            let for_export_bundle se1 uu____7491 =
              match uu____7491 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7530,uu____7531) ->
                       let dec =
                         let uu___93_7541 = se1  in
                         let uu____7542 =
                           let uu____7543 =
                             let uu____7550 =
                               let uu____7553 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7553  in
                             (l, us, uu____7550)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7543  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7542;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7541.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7541.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7541.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7565,uu____7566,uu____7567) ->
                       let dec =
                         let uu___94_7573 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___94_7573.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___94_7573.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___94_7573.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7578 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7600,uu____7601,uu____7602) ->
          let uu____7603 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7603 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7624 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7624
          then
            ([(let uu___95_7640 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___95_7640.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___95_7640.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___95_7640.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7642 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_7646  ->
                       match uu___59_7646 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7647 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7652 -> true
                       | uu____7653 -> false))
                in
             if uu____7642 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7671 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7676 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7681 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7686 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7691 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7709) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7726 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7726
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
          let uu____7757 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7757
          then
            let uu____7766 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___96_7779 = se  in
                      let uu____7780 =
                        let uu____7781 =
                          let uu____7788 =
                            let uu____7789 =
                              let uu____7792 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7792.FStar_Syntax_Syntax.fv_name  in
                            uu____7789.FStar_Syntax_Syntax.v  in
                          (uu____7788, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7781  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7780;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___96_7779.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___96_7779.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___96_7779.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7766, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7812 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7829 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7844) ->
          let env1 =
            let uu____7848 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7848 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7850 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7851 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7861 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7861) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7862,uu____7863,uu____7864) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7868  ->
                  match uu___60_7868 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7869 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7870,uu____7871) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7879  ->
                  match uu___60_7879 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7880 -> false))
          -> env
      | uu____7881 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7941 se =
        match uu____7941 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7994 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7994
              then
                let uu____7995 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7995
              else ());
             (let uu____7997 = tc_decl env1 se  in
              match uu____7997 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____8047 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____8047
                             then
                               let uu____8048 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____8048
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
                    (let uu____8071 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____8071
                     then
                       let uu____8072 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8078 =
                                  let uu____8079 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____8079 "\n"  in
                                Prims.strcat s uu____8078) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____8072
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8084 =
                       let uu____8093 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____8093
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____8128 se1 =
                            match uu____8128 with
                            | (exports1,hidden1) ->
                                let uu____8156 = for_export hidden1 se1  in
                                (match uu____8156 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____8084 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___97_8235 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___97_8235.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___97_8235.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___97_8235.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___97_8235.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8313 = acc  in
        match uu____8313 with
        | (uu____8348,uu____8349,env1,uu____8351) ->
            let uu____8364 =
              FStar_Util.record_time
                (fun uu____8410  -> process_one_decl acc se)
               in
            (match uu____8364 with
             | (r,ms_elapsed) ->
                 ((let uu____8474 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8474
                   then
                     let uu____8475 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8476 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8475 uu____8476
                   else ());
                  r))
         in
      let uu____8478 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8478 with
      | (ses1,exports,env1,uu____8526) ->
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
          let uu___98_8557 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___98_8557.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___98_8557.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___98_8557.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___98_8557.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___98_8557.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___98_8557.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___98_8557.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___98_8557.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___98_8557.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___98_8557.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___98_8557.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___98_8557.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___98_8557.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___98_8557.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___98_8557.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___98_8557.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___98_8557.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___98_8557.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___98_8557.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___98_8557.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___98_8557.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___98_8557.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___98_8557.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___98_8557.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___98_8557.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___98_8557.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___98_8557.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___98_8557.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___98_8557.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___98_8557.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___98_8557.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___98_8557.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8568 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8568 with
          | (univs2,t1) ->
              ((let uu____8576 =
                  let uu____8577 =
                    let uu____8580 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8580  in
                  FStar_All.pipe_left uu____8577
                    (FStar_Options.Other "Exports")
                   in
                if uu____8576
                then
                  let uu____8581 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8582 =
                    let uu____8583 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8583
                      (FStar_String.concat ", ")
                     in
                  let uu____8592 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8581 uu____8582 uu____8592
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8595 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8595 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8619 =
             let uu____8620 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8621 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8620 uu____8621
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8619);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8628) ->
              let uu____8637 =
                let uu____8638 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8638  in
              if uu____8637
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8648,uu____8649) ->
              let t =
                let uu____8661 =
                  let uu____8664 =
                    let uu____8665 =
                      let uu____8678 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8678)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8665  in
                  FStar_Syntax_Syntax.mk uu____8664  in
                uu____8661 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8685,uu____8686,uu____8687) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8695 =
                let uu____8696 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8696  in
              if uu____8695 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8700,lbs),uu____8702) ->
              let uu____8717 =
                let uu____8718 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8718  in
              if uu____8717
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
              let uu____8737 =
                let uu____8738 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8738  in
              if uu____8737
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8745 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8746 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8753 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8754 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8755 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8756 -> ()  in
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
             | FStar_Syntax_Syntax.Projector (l,uu____8833) -> true
             | uu____8834 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8853 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8884 ->
                   let uu____8885 =
                     let uu____8888 =
                       let uu____8889 =
                         let uu____8902 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8902)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8889  in
                     FStar_Syntax_Syntax.mk uu____8888  in
                   uu____8885 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8910,uu____8911) ->
            let s1 =
              let uu___99_8921 = s  in
              let uu____8922 =
                let uu____8923 =
                  let uu____8930 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8930)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8923  in
              let uu____8931 =
                let uu____8934 =
                  let uu____8937 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____8937  in
                FStar_Syntax_Syntax.Assumption :: uu____8934  in
              {
                FStar_Syntax_Syntax.sigel = uu____8922;
                FStar_Syntax_Syntax.sigrng =
                  (uu___99_8921.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8931;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___99_8921.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___99_8921.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____8940 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8954 =
        match uu____8954 with
        | (uvs,t) ->
            let uu___100_8961 = s  in
            let uu____8962 =
              let uu____8965 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____8965  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___100_8961.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____8962;
              FStar_Syntax_Syntax.sigmeta =
                (uu___100_8961.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___100_8961.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____8977 -> failwith "Impossible!"  in
        let c_opt =
          let uu____8981 = FStar_Syntax_Util.is_unit t  in
          if uu____8981
          then
            let uu____8984 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____8984
          else
            (let uu____8986 =
               let uu____8987 = FStar_Syntax_Subst.compress t  in
               uu____8987.FStar_Syntax_Syntax.n  in
             match uu____8986 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____8992,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____9012 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           let uu____9021 = FStar_Syntax_Util.is_pure_or_ghost_comp c  in
           if uu____9021
           then
             let uu____9022 =
               let uu____9023 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
               FStar_All.pipe_right uu____9023 FStar_Syntax_Util.is_unit  in
             Prims.op_Negation uu____9022
           else
             (let uu____9031 = comp_effect_name1 c  in
              FStar_TypeChecker_Env.is_reifiable_effect env uu____9031))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9040 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9059 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9107,uu____9108,uu____9109,uu____9110,uu____9111)
                         ->
                         ((let uu____9121 =
                             let uu____9124 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____9124  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____9121);
                          (let uu____9217 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____9217 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9221,uu____9222,uu____9223,uu____9224,uu____9225)
                         ->
                         ((let uu____9231 =
                             let uu____9234 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9234  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9231);
                          sigelts1)
                     | uu____9327 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9334 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9334
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9340 =
                   let uu___101_9341 = s  in
                   let uu____9342 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___101_9341.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___101_9341.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9342;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___101_9341.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___101_9341.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9340])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9352 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9352
            then []
            else
              (let uu____9356 = lbs  in
               match uu____9356 with
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
                       (fun uu____9412  ->
                          match uu____9412 with
                          | (uu____9419,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9437  ->
                            match uu____9437 with
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
                          (fun uu____9457  ->
                             match uu____9457 with
                             | (uu____9464,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9477,uu____9478) ->
            let is_haseq = FStar_TypeChecker_Util.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9483 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9534 =
                       FStar_TypeChecker_Util.get_haseq_axiom_lid l  in
                     FStar_Ident.lid_equals lid uu____9534) uu____9483
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9537 =
                   let uu___102_9538 = s  in
                   let uu____9539 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___102_9538.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___102_9538.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9539;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___102_9538.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___102_9538.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9537]
               else [])
            else
              (let uu____9544 =
                 let uu___103_9545 = s  in
                 let uu____9546 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___103_9545.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___103_9545.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9546;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___103_9545.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___103_9545.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9544])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9549 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9550 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9551 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9552 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9565 -> [s]  in
      let uu___104_9566 = m  in
      let uu____9567 =
        let uu____9568 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9568  in
      {
        FStar_Syntax_Syntax.name = (uu___104_9566.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9567;
        FStar_Syntax_Syntax.exports =
          (uu___104_9566.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____9582 = FStar_Syntax_DsEnv.pop ()  in
       FStar_All.pipe_right uu____9582 FStar_Pervasives.ignore);
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
      let uu___105_9593 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___105_9593.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___105_9593.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___105_9593.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___105_9593.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___105_9593.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___105_9593.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___105_9593.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___105_9593.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___105_9593.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___105_9593.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___105_9593.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___105_9593.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___105_9593.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___105_9593.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___105_9593.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___105_9593.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___105_9593.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___105_9593.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___105_9593.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___105_9593.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___105_9593.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___105_9593.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___105_9593.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___105_9593.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___105_9593.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___105_9593.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___105_9593.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___105_9593.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___105_9593.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___105_9593.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___105_9593.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___105_9593.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___105_9593.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___105_9593.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____9614 = FStar_Options.debug_any ()  in
       if uu____9614
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
         let uu___106_9619 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___106_9619.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___106_9619.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___106_9619.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___106_9619.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___106_9619.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___106_9619.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___106_9619.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___106_9619.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___106_9619.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___106_9619.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___106_9619.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___106_9619.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___106_9619.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___106_9619.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___106_9619.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___106_9619.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___106_9619.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___106_9619.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___106_9619.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___106_9619.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___106_9619.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___106_9619.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___106_9619.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___106_9619.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___106_9619.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___106_9619.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___106_9619.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___106_9619.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___106_9619.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___106_9619.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___106_9619.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___106_9619.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___106_9619.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____9621 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____9621 with
       | (ses,exports,env3) ->
           ((let uu___107_9654 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___107_9654.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___107_9654.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___107_9654.FStar_Syntax_Syntax.is_interface)
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
        let uu____9676 = tc_decls env decls  in
        match uu____9676 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___108_9707 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___108_9707.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___108_9707.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___108_9707.FStar_Syntax_Syntax.is_interface)
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
          let uu___109_9752 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___109_9752.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___109_9752.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___109_9752.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___109_9752.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___109_9752.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___109_9752.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___109_9752.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___109_9752.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___109_9752.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___109_9752.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___109_9752.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___109_9752.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___109_9752.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___109_9752.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___109_9752.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___109_9752.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___109_9752.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___109_9752.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___109_9752.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___109_9752.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___109_9752.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___109_9752.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___109_9752.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___109_9752.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___109_9752.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___109_9752.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___109_9752.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___109_9752.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___109_9752.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___109_9752.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___109_9752.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___109_9752.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___109_9752.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___109_9752.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env02 = push_context env01 msg  in
      let uu____9756 = tc_partial_modul env02 m  in
      match uu____9756 with
      | (modul,non_private_decls,env) ->
          let uu____9780 =
            finish_partial_modul false env modul non_private_decls  in
          (match uu____9780 with
           | (m1,m_opt,env1) ->
               (m1, m_opt,
                 (let uu___110_9807 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___110_9807.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___110_9807.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___110_9807.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___110_9807.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___110_9807.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___110_9807.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___110_9807.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___110_9807.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___110_9807.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___110_9807.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___110_9807.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___110_9807.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___110_9807.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___110_9807.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___110_9807.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___110_9807.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___110_9807.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___110_9807.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___110_9807.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___110_9807.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___110_9807.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___110_9807.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___110_9807.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___110_9807.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___110_9807.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___110_9807.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___110_9807.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___110_9807.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth =
                      (uu___110_9807.FStar_TypeChecker_Env.synth);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___110_9807.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___110_9807.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___110_9807.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___110_9807.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___110_9807.FStar_TypeChecker_Env.dep_graph)
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
          let uu____9822 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____9822
          then
            let en0 =
              pop_context en
                (Prims.strcat "Ending modul "
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            let en01 =
              let uu___111_9833 = en0  in
              let uu____9834 =
                let uu____9847 =
                  FStar_All.pipe_right
                    en.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                (uu____9847, FStar_Pervasives_Native.None)  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___111_9833.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___111_9833.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___111_9833.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___111_9833.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___111_9833.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___111_9833.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___111_9833.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___111_9833.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___111_9833.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___111_9833.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___111_9833.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___111_9833.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___111_9833.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___111_9833.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___111_9833.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___111_9833.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___111_9833.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___111_9833.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___111_9833.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___111_9833.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___111_9833.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___111_9833.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___111_9833.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___111_9833.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___111_9833.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___111_9833.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___111_9833.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index = uu____9834;
                FStar_TypeChecker_Env.proof_ns =
                  (uu___111_9833.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___111_9833.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___111_9833.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___111_9833.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___111_9833.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___111_9833.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___111_9833.FStar_TypeChecker_Env.dep_graph)
              }  in
            ((let uu____9885 =
                let uu____9886 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9886  in
              if uu____9885
              then
                let uu____9887 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____9887 FStar_Pervasives.ignore
              else ());
             (let modul_iface = extract_interface en m  in
              (let uu____9891 =
                 let uu____9892 =
                   FStar_Options.should_verify
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____9892 then "" else " (in lax mode) "  in
               let uu____9894 =
                 let uu____9895 =
                   FStar_Options.dump_module
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____9895
                 then
                   let uu____9896 =
                     let uu____9897 = FStar_Syntax_Print.modul_to_string m
                        in
                     Prims.strcat uu____9897 "\n"  in
                   Prims.strcat "\nfrom: " uu____9896
                 else ""  in
               let uu____9899 =
                 let uu____9900 =
                   FStar_Options.dump_module
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____9900
                 then
                   let uu____9901 =
                     let uu____9902 =
                       FStar_Syntax_Print.modul_to_string modul_iface  in
                     Prims.strcat uu____9902 "\n"  in
                   Prims.strcat "\nto: " uu____9901
                 else ""  in
               FStar_Util.print4
                 "Extracting and type checking module %s interface%s%s%s\n"
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____9891
                 uu____9894 uu____9899);
              (let env0 =
                 let uu___112_9905 = en01  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___112_9905.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___112_9905.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___112_9905.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___112_9905.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___112_9905.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___112_9905.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___112_9905.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___112_9905.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___112_9905.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___112_9905.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___112_9905.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___112_9905.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___112_9905.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___112_9905.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___112_9905.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___112_9905.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface = true;
                   FStar_TypeChecker_Env.admit =
                     (uu___112_9905.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___112_9905.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___112_9905.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___112_9905.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___112_9905.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___112_9905.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___112_9905.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___112_9905.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___112_9905.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___112_9905.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___112_9905.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___112_9905.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___112_9905.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___112_9905.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___112_9905.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___112_9905.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___112_9905.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___112_9905.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let uu____9906 = tc_modul en01 modul_iface  in
               match uu____9906 with
               | (modul_iface1,must_be_none,env) ->
                   if must_be_none <> FStar_Pervasives_Native.None
                   then
                     failwith
                       "Impossible! Expected the second component to be None"
                   else (m, (FStar_Pervasives_Native.Some modul_iface1), env))))
          else
            (let modul =
               let uu____9953 = FStar_Options.use_extracted_interfaces ()  in
               if uu____9953
               then
                 let uu___113_9954 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___113_9954.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___113_9954.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___113_9954.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___114_9956 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___114_9956.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___114_9956.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___114_9956.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____9959 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____9959 FStar_Util.smap_clear);
             (let uu____9987 =
                ((let uu____9990 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____9990) &&
                   (let uu____9992 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____9992))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____9987 then check_exports env modul exports else ());
             (let uu____9995 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____9995 FStar_Pervasives.ignore);
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____9999 =
                let uu____10000 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____10000  in
              if uu____9999
              then
                let uu____10001 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____10001 FStar_Pervasives.ignore
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
        let uu____10013 =
          let uu____10014 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____10014  in
        push_context env uu____10013  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____10033 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____10054 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____10054 with | (uu____10063,uu____10064,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____10085 = FStar_Options.debug_any ()  in
       if uu____10085
       then
         let uu____10086 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____10086
       else ());
      (let env1 =
         let uu___115_10090 = env  in
         let uu____10091 =
           let uu____10092 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____10092  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___115_10090.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___115_10090.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___115_10090.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___115_10090.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___115_10090.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___115_10090.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___115_10090.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___115_10090.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___115_10090.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___115_10090.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___115_10090.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___115_10090.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___115_10090.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___115_10090.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___115_10090.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___115_10090.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___115_10090.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___115_10090.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____10091;
           FStar_TypeChecker_Env.lax_universes =
             (uu___115_10090.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___115_10090.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___115_10090.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___115_10090.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___115_10090.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___115_10090.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___115_10090.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___115_10090.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___115_10090.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___115_10090.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___115_10090.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___115_10090.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___115_10090.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___115_10090.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___115_10090.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___115_10090.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____10093 = tc_modul env1 m  in
       match uu____10093 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____10118 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____10118
             then
               let uu____10119 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____10119
             else ());
            (let uu____10122 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____10122
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
                       let uu____10153 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____10153 with
                       | (univnames1,e) ->
                           let uu___116_10160 = lb  in
                           let uu____10161 =
                             let uu____10164 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____10164 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___116_10160.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___116_10160.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___116_10160.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___116_10160.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____10161;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___116_10160.FStar_Syntax_Syntax.lbattrs)
                           }
                        in
                     let uu___117_10165 = se  in
                     let uu____10166 =
                       let uu____10167 =
                         let uu____10174 =
                           let uu____10181 = FStar_List.map update lbs  in
                           (b, uu____10181)  in
                         (uu____10174, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____10167  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____10166;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___117_10165.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___117_10165.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___117_10165.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___117_10165.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____10194 -> se  in
               let normalized_module =
                 let uu___118_10196 = m1  in
                 let uu____10197 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___118_10196.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____10197;
                   FStar_Syntax_Syntax.exports =
                     (uu___118_10196.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___118_10196.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10198 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10198
             else ());
            (m1, m_iface_opt, env2)))
  