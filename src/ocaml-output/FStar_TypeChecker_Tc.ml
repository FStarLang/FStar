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
  
let get_tactic_fv :
  'Auu____147 .
    'Auu____147 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____163) ->
            let uu____168 =
              let uu____169 = FStar_Syntax_Subst.compress h'  in
              uu____169.FStar_Syntax_Syntax.n  in
            (match uu____168 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____175 -> FStar_Pervasives_Native.None)
        | uu____176 -> FStar_Pervasives_Native.None
  
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
        let uu____218 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____218 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____239 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____239
         then
           let uu____240 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____240
         else ());
        (let uu____242 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____242 with
         | (t',uu____250,uu____251) ->
             ((let uu____253 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____253
               then
                 let uu____254 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____254
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
        let uu____265 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____265
  
let check_nogen :
  'Auu____270 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____270 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____290 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____290)
  
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
        let fail uu____317 =
          let uu____318 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          FStar_Errors.raise_error uu____318 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____362)::(wp,uu____364)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____379 -> fail ())
        | uu____380 -> fail ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____387 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____387 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____413 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____413 t  in
          let open_univs_binders n_binders bs =
            let uu____423 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____423 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____431 =
            let uu____438 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____439 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____438 uu____439  in
          (match uu____431 with
           | (effect_params_un,signature_un,opening) ->
               let uu____449 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____449 with
                | (effect_params,env,uu____458) ->
                    let uu____459 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____459 with
                     | (signature,uu____465) ->
                         let ed1 =
                           let uu___63_467 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___63_467.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___63_467.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___63_467.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___63_467.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___63_467.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___63_467.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___63_467.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___63_467.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___63_467.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___63_467.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___63_467.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___63_467.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___63_467.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___63_467.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___63_467.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___63_467.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___63_467.FStar_Syntax_Syntax.actions)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____483 ->
                               let op uu____505 =
                                 match uu____505 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____525 =
                                       let uu____526 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____535 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____526
                                         uu____535
                                        in
                                     (us, uu____525)
                                  in
                               let uu___64_544 = ed1  in
                               let uu____545 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____546 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____547 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____548 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____549 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____550 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____551 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____552 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____553 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____554 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____555 =
                                 let uu____556 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____556  in
                               let uu____567 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____568 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____569 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___65_577 = a  in
                                      let uu____578 =
                                        let uu____579 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____579
                                         in
                                      let uu____590 =
                                        let uu____591 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____591
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___65_577.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___65_577.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___65_577.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___65_577.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____578;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____590
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___64_544.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___64_544.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___64_544.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___64_544.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____545;
                                 FStar_Syntax_Syntax.bind_wp = uu____546;
                                 FStar_Syntax_Syntax.if_then_else = uu____547;
                                 FStar_Syntax_Syntax.ite_wp = uu____548;
                                 FStar_Syntax_Syntax.stronger = uu____549;
                                 FStar_Syntax_Syntax.close_wp = uu____550;
                                 FStar_Syntax_Syntax.assert_p = uu____551;
                                 FStar_Syntax_Syntax.assume_p = uu____552;
                                 FStar_Syntax_Syntax.null_wp = uu____553;
                                 FStar_Syntax_Syntax.trivial = uu____554;
                                 FStar_Syntax_Syntax.repr = uu____555;
                                 FStar_Syntax_Syntax.return_repr = uu____567;
                                 FStar_Syntax_Syntax.bind_repr = uu____568;
                                 FStar_Syntax_Syntax.actions = uu____569
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____628 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____628
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____639 =
                             let uu____640 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____640.FStar_Syntax_Syntax.n  in
                           match uu____639 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____675)::(wp,uu____677)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____692 -> fail signature1)
                           | uu____693 -> fail signature1  in
                         let uu____694 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____694 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____716 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____723 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____723 with
                                     | (signature1,uu____735) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____736 ->
                                    let uu____739 =
                                      let uu____744 =
                                        let uu____745 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____745)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____744
                                       in
                                    (match uu____739 with
                                     | (uu____754,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____757 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____757
                                 in
                              ((let uu____759 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____759
                                then
                                  let uu____760 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____761 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____762 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____763 =
                                    let uu____764 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____764
                                     in
                                  let uu____765 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____760 uu____761 uu____762 uu____763
                                    uu____765
                                else ());
                               (let check_and_gen' env2 uu____781 k =
                                  match uu____781 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____795::uu____796 ->
                                           let uu____799 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____799 with
                                            | (us1,t1) ->
                                                let uu____808 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____808 with
                                                 | (us2,t2) ->
                                                     let uu____815 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____816 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____816))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____821 =
                                      let uu____828 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____829 =
                                        let uu____832 =
                                          let uu____833 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____833
                                           in
                                        [uu____832]  in
                                      uu____828 :: uu____829  in
                                    let uu____834 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____821
                                      uu____834
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____838 = fresh_effect_signature ()
                                     in
                                  match uu____838 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____854 =
                                          let uu____861 =
                                            let uu____862 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____862
                                             in
                                          [uu____861]  in
                                        let uu____863 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____854
                                          uu____863
                                         in
                                      let expected_k =
                                        let uu____869 =
                                          let uu____876 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____877 =
                                            let uu____880 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____881 =
                                              let uu____884 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____885 =
                                                let uu____888 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____889 =
                                                  let uu____892 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____892]  in
                                                uu____888 :: uu____889  in
                                              uu____884 :: uu____885  in
                                            uu____880 :: uu____881  in
                                          uu____876 :: uu____877  in
                                        let uu____893 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____869
                                          uu____893
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____898 =
                                      let uu____899 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____899
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____898
                                     in
                                  let expected_k =
                                    let uu____911 =
                                      let uu____918 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____919 =
                                        let uu____922 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____923 =
                                          let uu____926 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____927 =
                                            let uu____930 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____930]  in
                                          uu____926 :: uu____927  in
                                        uu____922 :: uu____923  in
                                      uu____918 :: uu____919  in
                                    let uu____931 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____911
                                      uu____931
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____938 =
                                      let uu____945 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____946 =
                                        let uu____949 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____949]  in
                                      uu____945 :: uu____946  in
                                    let uu____950 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____938
                                      uu____950
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____954 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____954 with
                                  | (t,uu____960) ->
                                      let expected_k =
                                        let uu____964 =
                                          let uu____971 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____972 =
                                            let uu____975 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____976 =
                                              let uu____979 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____979]  in
                                            uu____975 :: uu____976  in
                                          uu____971 :: uu____972  in
                                        let uu____980 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____964
                                          uu____980
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____985 =
                                      let uu____986 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____986
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____985
                                     in
                                  let b_wp_a =
                                    let uu____998 =
                                      let uu____1005 =
                                        let uu____1006 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1006
                                         in
                                      [uu____1005]  in
                                    let uu____1007 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____998
                                      uu____1007
                                     in
                                  let expected_k =
                                    let uu____1013 =
                                      let uu____1020 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1021 =
                                        let uu____1024 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1025 =
                                          let uu____1028 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1028]  in
                                        uu____1024 :: uu____1025  in
                                      uu____1020 :: uu____1021  in
                                    let uu____1029 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1013
                                      uu____1029
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1036 =
                                      let uu____1043 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1044 =
                                        let uu____1047 =
                                          let uu____1048 =
                                            let uu____1049 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1049
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1048
                                           in
                                        let uu____1058 =
                                          let uu____1061 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1061]  in
                                        uu____1047 :: uu____1058  in
                                      uu____1043 :: uu____1044  in
                                    let uu____1062 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1036
                                      uu____1062
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1069 =
                                      let uu____1076 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1077 =
                                        let uu____1080 =
                                          let uu____1081 =
                                            let uu____1082 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1082
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1081
                                           in
                                        let uu____1091 =
                                          let uu____1094 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1094]  in
                                        uu____1080 :: uu____1091  in
                                      uu____1076 :: uu____1077  in
                                    let uu____1095 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1069
                                      uu____1095
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1102 =
                                      let uu____1109 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1109]  in
                                    let uu____1110 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1102
                                      uu____1110
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1114 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1114 with
                                  | (t,uu____1120) ->
                                      let expected_k =
                                        let uu____1124 =
                                          let uu____1131 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1132 =
                                            let uu____1135 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1135]  in
                                          uu____1131 :: uu____1132  in
                                        let uu____1136 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1124
                                          uu____1136
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1139 =
                                  let uu____1150 =
                                    let uu____1151 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1151.FStar_Syntax_Syntax.n  in
                                  match uu____1150 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1166 ->
                                      let repr =
                                        let uu____1168 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1168 with
                                        | (t,uu____1174) ->
                                            let expected_k =
                                              let uu____1178 =
                                                let uu____1185 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1186 =
                                                  let uu____1189 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1189]  in
                                                uu____1185 :: uu____1186  in
                                              let uu____1190 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1178 uu____1190
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
                                        let uu____1203 =
                                          let uu____1206 =
                                            let uu____1207 =
                                              let uu____1222 =
                                                let uu____1225 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1226 =
                                                  let uu____1229 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1229]  in
                                                uu____1225 :: uu____1226  in
                                              (repr1, uu____1222)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1207
                                             in
                                          FStar_Syntax_Syntax.mk uu____1206
                                           in
                                        uu____1203
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1244 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1244 wp  in
                                      let destruct_repr t =
                                        let uu____1257 =
                                          let uu____1258 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1258.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1257 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1269,(t1,uu____1271)::
                                             (wp,uu____1273)::[])
                                            -> (t1, wp)
                                        | uu____1316 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1327 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1327
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1328 =
                                          fresh_effect_signature ()  in
                                        match uu____1328 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1344 =
                                                let uu____1351 =
                                                  let uu____1352 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1352
                                                   in
                                                [uu____1351]  in
                                              let uu____1353 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1344 uu____1353
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
                                              let uu____1359 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1359
                                               in
                                            let wp_g_x =
                                              let uu____1363 =
                                                let uu____1364 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1365 =
                                                  let uu____1366 =
                                                    let uu____1367 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1367
                                                     in
                                                  [uu____1366]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1364 uu____1365
                                                 in
                                              uu____1363
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1376 =
                                                  let uu____1377 =
                                                    let uu____1378 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1378
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1387 =
                                                    let uu____1388 =
                                                      let uu____1391 =
                                                        let uu____1394 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1395 =
                                                          let uu____1398 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1399 =
                                                            let uu____1402 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1403 =
                                                              let uu____1406
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1406]
                                                               in
                                                            uu____1402 ::
                                                              uu____1403
                                                             in
                                                          uu____1398 ::
                                                            uu____1399
                                                           in
                                                        uu____1394 ::
                                                          uu____1395
                                                         in
                                                      r :: uu____1391  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1388
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1377 uu____1387
                                                   in
                                                uu____1376
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let expected_k =
                                              let uu____1412 =
                                                let uu____1419 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1420 =
                                                  let uu____1423 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____1424 =
                                                    let uu____1427 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1428 =
                                                      let uu____1431 =
                                                        let uu____1432 =
                                                          let uu____1433 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1433
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1432
                                                         in
                                                      let uu____1434 =
                                                        let uu____1437 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1438 =
                                                          let uu____1441 =
                                                            let uu____1442 =
                                                              let uu____1443
                                                                =
                                                                let uu____1450
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1450]
                                                                 in
                                                              let uu____1451
                                                                =
                                                                let uu____1454
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1454
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1443
                                                                uu____1451
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1442
                                                             in
                                                          [uu____1441]  in
                                                        uu____1437 ::
                                                          uu____1438
                                                         in
                                                      uu____1431 ::
                                                        uu____1434
                                                       in
                                                    uu____1427 :: uu____1428
                                                     in
                                                  uu____1423 :: uu____1424
                                                   in
                                                uu____1419 :: uu____1420  in
                                              let uu____1455 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1412 uu____1455
                                               in
                                            let uu____1458 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1458 with
                                             | (expected_k1,uu____1466,uu____1467)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___66_1472 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___66_1472.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1482 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1482
                                           in
                                        let res =
                                          let wp =
                                            let uu____1489 =
                                              let uu____1490 =
                                                let uu____1491 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1491
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1500 =
                                                let uu____1501 =
                                                  let uu____1504 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1505 =
                                                    let uu____1508 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1508]  in
                                                  uu____1504 :: uu____1505
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1501
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1490 uu____1500
                                               in
                                            uu____1489
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1514 =
                                            let uu____1521 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1522 =
                                              let uu____1525 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1525]  in
                                            uu____1521 :: uu____1522  in
                                          let uu____1526 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1514
                                            uu____1526
                                           in
                                        let uu____1529 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1529 with
                                        | (expected_k1,uu____1543,uu____1544)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1548 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1548 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1569 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let act_typ =
                                            let uu____1597 =
                                              let uu____1598 =
                                                FStar_Syntax_Subst.compress
                                                  act.FStar_Syntax_Syntax.action_typ
                                                 in
                                              uu____1598.FStar_Syntax_Syntax.n
                                               in
                                            match uu____1597 with
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
                                                  let uu____1624 =
                                                    let uu____1627 =
                                                      let uu____1628 =
                                                        let uu____1629 =
                                                          FStar_List.hd
                                                            c1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        FStar_Pervasives_Native.fst
                                                          uu____1629
                                                         in
                                                      mk_repr'
                                                        c1.FStar_Syntax_Syntax.result_typ
                                                        uu____1628
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total
                                                      uu____1627
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____1624
                                                else
                                                  act.FStar_Syntax_Syntax.action_typ
                                            | uu____1645 ->
                                                act.FStar_Syntax_Syntax.action_typ
                                             in
                                          let uu____1646 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1 act_typ
                                             in
                                          match uu____1646 with
                                          | (act_typ1,uu____1654,g_t) ->
                                              let env' =
                                                let uu___67_1657 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ1
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___67_1657.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___67_1657.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1659 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1659
                                                then
                                                  let uu____1660 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1661 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ1
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1660 uu____1661
                                                else ());
                                               (let uu____1663 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1663 with
                                                | (act_defn,uu____1671,g_a)
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
                                                    let uu____1675 =
                                                      let act_typ3 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ2
                                                         in
                                                      match act_typ3.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1703 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1703
                                                           with
                                                           | (bs1,uu____1713)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1720
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1720
                                                                  in
                                                               let uu____1723
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1723
                                                                with
                                                                | (k1,uu____1735,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1737 ->
                                                          let uu____1738 =
                                                            let uu____1743 =
                                                              let uu____1744
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ3
                                                                 in
                                                              let uu____1745
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ3
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1744
                                                                uu____1745
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1743)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1738
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1675 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ2
                                                             expected_k
                                                            in
                                                         ((let uu____1754 =
                                                             let uu____1755 =
                                                               let uu____1756
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1756
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1755
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1754);
                                                          (let act_typ3 =
                                                             let uu____1760 =
                                                               let uu____1761
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1761.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1760
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1784
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1784
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1793
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1793
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1815
                                                                    =
                                                                    let uu____1816
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1816]
                                                                     in
                                                                    let uu____1817
                                                                    =
                                                                    let uu____1826
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1826]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1815;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1817;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1827
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1827))
                                                             | uu____1830 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1833 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1833
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
                                                               let uu___68_1842
                                                                 = act  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___68_1842.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___68_1842.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___68_1842.FStar_Syntax_Syntax.action_params);
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
                                match uu____1139 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1866 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1866
                                       in
                                    let uu____1869 =
                                      let uu____1876 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1876 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1897 ->
                                               let uu____1900 =
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
                                               if uu____1900
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1914 =
                                                    let uu____1919 =
                                                      let uu____1920 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1921 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1920 uu____1921
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1919)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1914
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1869 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1935 =
                                             let uu____1940 =
                                               let uu____1941 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1941.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1940)  in
                                           match uu____1935 with
                                           | ([],uu____1944) -> t
                                           | (uu____1955,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1956,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1974 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1987 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1987
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1992 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1994 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1994))
                                                && (m <> n1)
                                               in
                                            if uu____1992
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____2010 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____2017 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____2018 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2010 uu____2017
                                                  uu____2018
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____2026 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____2026 with
                                           | (univs2,defn) ->
                                               let uu____2033 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____2033 with
                                                | (univs',typ) ->
                                                    let uu___69_2043 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___69_2043.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___69_2043.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___69_2043.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___70_2048 = ed2  in
                                           let uu____2049 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____2050 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____2051 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____2052 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____2053 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____2054 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____2055 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____2056 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____2057 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____2058 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____2059 =
                                             let uu____2060 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____2060
                                              in
                                           let uu____2071 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____2072 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2073 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___70_2048.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___70_2048.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2049;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2050;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2051;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2052;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2053;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2054;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2055;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2056;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2057;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2058;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2059;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2071;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2072;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2073
                                           }  in
                                         ((let uu____2077 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2077
                                           then
                                             let uu____2078 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2078
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
      let uu____2096 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2096 with
      | (effect_binders_un,signature_un) ->
          let uu____2113 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2113 with
           | (effect_binders,env1,uu____2132) ->
               let uu____2133 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2133 with
                | (signature,uu____2149) ->
                    let raise_error1 a uu____2160 =
                      match uu____2160 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2186  ->
                           match uu____2186 with
                           | (bv,qual) ->
                               let uu____2197 =
                                 let uu___71_2198 = bv  in
                                 let uu____2199 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___71_2198.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___71_2198.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2199
                                 }  in
                               (uu____2197, qual)) effect_binders
                       in
                    let uu____2202 =
                      let uu____2209 =
                        let uu____2210 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2210.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2209 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2220)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2242 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2202 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2260 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2260
                           then
                             let uu____2261 =
                               let uu____2264 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2264  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2261
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2298 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2298 with
                           | (t2,comp,uu____2311) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2318 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2318 with
                          | (repr,_comp) ->
                              ((let uu____2340 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2340
                                then
                                  let uu____2341 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2341
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
                                  let uu____2347 =
                                    let uu____2348 =
                                      let uu____2349 =
                                        let uu____2364 =
                                          let uu____2371 =
                                            let uu____2376 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2377 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2376, uu____2377)  in
                                          [uu____2371]  in
                                        (wp_type1, uu____2364)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2349
                                       in
                                    mk1 uu____2348  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2347
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2402 =
                                      let uu____2407 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2407)  in
                                    let uu____2408 =
                                      let uu____2415 =
                                        let uu____2416 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2416
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2415]  in
                                    uu____2402 :: uu____2408  in
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
                                  let uu____2479 = item  in
                                  match uu____2479 with
                                  | (u_item,item1) ->
                                      let uu____2500 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2500 with
                                       | (item2,item_comp) ->
                                           ((let uu____2516 =
                                               let uu____2517 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2517
                                                in
                                             if uu____2516
                                             then
                                               let uu____2518 =
                                                 let uu____2523 =
                                                   let uu____2524 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2525 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2524 uu____2525
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2523)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2518
                                             else ());
                                            (let uu____2527 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2527 with
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
                                let uu____2547 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2547 with
                                | (dmff_env1,uu____2571,bind_wp,bind_elab) ->
                                    let uu____2574 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2574 with
                                     | (dmff_env2,uu____2598,return_wp,return_elab)
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
                                           let uu____2605 =
                                             let uu____2606 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2606.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2605 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2650 =
                                                       let uu____2665 =
                                                         let uu____2670 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2670
                                                          in
                                                       match uu____2665 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2734 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2650 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2773 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2773
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2790 =
                                                               let uu____2791
                                                                 =
                                                                 let uu____2806
                                                                   =
                                                                   let uu____2813
                                                                    =
                                                                    let uu____2818
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2819
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2818,
                                                                    uu____2819)
                                                                     in
                                                                   [uu____2813]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2806)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2791
                                                                in
                                                             mk1 uu____2790
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2834 =
                                                           let uu____2843 =
                                                             let uu____2844 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2844
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2843
                                                            in
                                                         (match uu____2834
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2863
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2865
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2865
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
                                                                    let uu____2871
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
                                                                    uu____2871
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
                                                                  let uu____2898
                                                                    =
                                                                    let uu____2899
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2900
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    let uu____2908
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2908,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2901]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2899
                                                                    uu____2900
                                                                     in
                                                                  uu____2898
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2933
                                                                  =
                                                                  let uu____2934
                                                                    =
                                                                    let uu____2941
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2941]
                                                                     in
                                                                  b11 ::
                                                                    uu____2934
                                                                   in
                                                                let uu____2946
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2933
                                                                  uu____2946
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2947 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2949 =
                                             let uu____2950 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2950.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2949 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2994 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2994
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____3007 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____3009 =
                                             let uu____3010 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____3010.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____3009 with
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
                                                     let uu____3037 =
                                                       let uu____3038 =
                                                         let uu____3041 =
                                                           let uu____3042 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3042
                                                            in
                                                         [uu____3041]  in
                                                       FStar_List.append
                                                         uu____3038 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____3037 body what)
                                              | uu____3043 ->
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
                                             (let uu____3061 =
                                                let uu____3062 =
                                                  let uu____3063 =
                                                    let uu____3078 =
                                                      let uu____3079 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3079
                                                       in
                                                    (t, uu____3078)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3063
                                                   in
                                                mk1 uu____3062  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3061)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3109 = f a2  in
                                               [uu____3109]
                                           | x::xs ->
                                               let uu____3114 =
                                                 apply_last1 f xs  in
                                               x :: uu____3114
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
                                           let uu____3134 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3134 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3164 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3164
                                                 then
                                                   let uu____3165 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3165
                                                 else ());
                                                (let uu____3167 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3167))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3176 =
                                                 let uu____3181 = mk_lid name
                                                    in
                                                 let uu____3182 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3181 uu____3182
                                                  in
                                               (match uu____3176 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3186 =
                                                        let uu____3189 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3189
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3186);
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
                                          (let uu____3286 =
                                             let uu____3289 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3290 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3289 :: uu____3290  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3286);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3388 =
                                               let uu____3391 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3392 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3391 :: uu____3392  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3388);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3487 =
                                                FStar_List.fold_left
                                                  (fun uu____3527  ->
                                                     fun action  ->
                                                       match uu____3527 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3548 =
                                                             let uu____3555 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3555
                                                               params_un
                                                              in
                                                           (match uu____3548
                                                            with
                                                            | (action_params,env',uu____3564)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3584
                                                                     ->
                                                                    match uu____3584
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3595
                                                                    =
                                                                    let uu___72_3596
                                                                    = bv  in
                                                                    let uu____3597
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___72_3596.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___72_3596.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3597
                                                                    }  in
                                                                    (uu____3595,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3601
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3601
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
                                                                    uu____3631
                                                                    ->
                                                                    let uu____3632
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3632
                                                                     in
                                                                    ((
                                                                    let uu____3636
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3636
                                                                    then
                                                                    let uu____3637
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3638
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3639
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3640
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3637
                                                                    uu____3638
                                                                    uu____3639
                                                                    uu____3640
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
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3647
                                                                    =
                                                                    let uu___73_3648
                                                                    = action
                                                                     in
                                                                    let uu____3649
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3650
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_3648.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_3648.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___73_3648.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3649;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3650
                                                                    }  in
                                                                    uu____3647
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3644))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3487 with
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
                                                      let uu____3683 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3684 =
                                                        let uu____3687 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3687]  in
                                                      uu____3683 ::
                                                        uu____3684
                                                       in
                                                    let uu____3688 =
                                                      let uu____3689 =
                                                        let uu____3690 =
                                                          let uu____3691 =
                                                            let uu____3706 =
                                                              let uu____3713
                                                                =
                                                                let uu____3718
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3719
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3718,
                                                                  uu____3719)
                                                                 in
                                                              [uu____3713]
                                                               in
                                                            (repr,
                                                              uu____3706)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3691
                                                           in
                                                        mk1 uu____3690  in
                                                      let uu____3734 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3689
                                                        uu____3734
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3688
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3737 =
                                                    let uu____3744 =
                                                      let uu____3745 =
                                                        let uu____3748 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3748
                                                         in
                                                      uu____3745.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3744 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3758)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3787
                                                                =
                                                                let uu____3804
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____3804
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3862
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____3787
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3912
                                                                    =
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3916
                                                                     in
                                                                    uu____3913.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3912
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3941
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____3941
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3954
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3979
                                                                     ->
                                                                    match uu____3979
                                                                    with
                                                                    | 
                                                                    (bv,uu____3985)
                                                                    ->
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3987
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3987
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3986
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3954
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
                                                                    let uu____4051
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4051
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4056
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4064
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4064
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4069
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4072
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4069,
                                                                    uu____4072)))
                                                                    | 
                                                                    uu____4079
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4080
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4086
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4085)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4080)))
                                                       | uu____4087 ->
                                                           Obj.repr
                                                             (let uu____4088
                                                                =
                                                                let uu____4093
                                                                  =
                                                                  let uu____4094
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4094
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4093)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4088))
                                                     in
                                                  (match uu____3737 with
                                                   | (pre,post) ->
                                                       ((let uu____4112 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4114 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4116 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___74_4118 =
                                                             ed  in
                                                           let uu____4119 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4120 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4121 =
                                                             let uu____4122 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4122)
                                                              in
                                                           let uu____4129 =
                                                             let uu____4130 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4130)
                                                              in
                                                           let uu____4137 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4138 =
                                                             let uu____4139 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4139)
                                                              in
                                                           let uu____4146 =
                                                             let uu____4147 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4147)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4119;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4120;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4121;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4129;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___74_4118.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4137;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4138;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4146;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____4154 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4154
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4172
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4172
                                                               then
                                                                 let uu____4173
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4173
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
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    let uu____4197
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4197)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4188
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
                                                                    uu____4185;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4212
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4212
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4214
                                                                 =
                                                                 let uu____4217
                                                                   =
                                                                   let uu____4220
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4220
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4217
                                                                   sigelts'
                                                                  in
                                                               (uu____4214,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4277 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4277 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4310 = FStar_List.hd ses  in
            uu____4310.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4315 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____4319,[],t,uu____4321,uu____4322);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4324;
               FStar_Syntax_Syntax.sigattrs = uu____4325;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____4327,_t_top,_lex_t_top,_0_40,uu____4330);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4332;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4333;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____4335,_t_cons,_lex_t_cons,_0_41,uu____4338);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4340;
                 FStar_Syntax_Syntax.sigattrs = uu____4341;_}::[]
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
                 let uu____4400 =
                   let uu____4403 =
                     let uu____4404 =
                       let uu____4411 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4411, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4404  in
                   FStar_Syntax_Syntax.mk uu____4403  in
                 uu____4400 FStar_Pervasives_Native.None r1  in
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
                   let uu____4429 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4429
                    in
                 let hd1 =
                   let uu____4431 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4431
                    in
                 let tl1 =
                   let uu____4433 =
                     let uu____4434 =
                       let uu____4437 =
                         let uu____4438 =
                           let uu____4445 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4445, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4438  in
                       FStar_Syntax_Syntax.mk uu____4437  in
                     uu____4434 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4433
                    in
                 let res =
                   let uu____4454 =
                     let uu____4457 =
                       let uu____4458 =
                         let uu____4465 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4465,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4458  in
                     FStar_Syntax_Syntax.mk uu____4457  in
                   uu____4454 FStar_Pervasives_Native.None r2  in
                 let uu____4471 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4471
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
               let uu____4510 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4510;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4515 ->
               let err_msg =
                 let uu____4519 =
                   let uu____4520 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4520  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4519
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
            let uu____4545 = FStar_Syntax_Util.type_u ()  in
            match uu____4545 with
            | (k,uu____4551) ->
                let phi1 =
                  let uu____4553 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4553
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4555 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4555 with
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
          let uu____4597 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4597 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4630 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4630 FStar_List.flatten  in
              ((let uu____4644 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4644
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
                          let uu____4655 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4665,uu____4666,uu____4667,uu____4668,uu____4669)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4678 -> failwith "Impossible!"  in
                          match uu____4655 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4689 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4693,uu____4694,uu____4695,uu____4696,uu____4697)
                        -> lid
                    | uu____4706 -> failwith "Impossible"  in
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
                  let uu____4724 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____4724
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
                     let uu____4747 =
                       let uu____4750 =
                         let uu____4751 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4751;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____4750 :: ses1  in
                     (uu____4747, data_ops_ses))
                   in
                (let uu____4761 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4795 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4820 ->
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
           let uu____4872 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____4872 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4910 = cps_and_elaborate env1 ne  in
           (match uu____4910 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___75_4947 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___75_4947.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___75_4947.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___75_4947.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___75_4947.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___76_4949 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4949.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4949.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4949.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4949.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___77_4957 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___77_4957.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___77_4957.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___77_4957.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___77_4957.FStar_Syntax_Syntax.sigattrs)
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
           let uu____4965 =
             let uu____4972 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4972
              in
           (match uu____4965 with
            | (a,wp_a_src) ->
                let uu____4987 =
                  let uu____4994 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4994
                   in
                (match uu____4987 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5010 =
                         let uu____5013 =
                           let uu____5014 =
                             let uu____5021 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5021)  in
                           FStar_Syntax_Syntax.NT uu____5014  in
                         [uu____5013]  in
                       FStar_Syntax_Subst.subst uu____5010 wp_b_tgt  in
                     let expected_k =
                       let uu____5025 =
                         let uu____5032 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5033 =
                           let uu____5036 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5036]  in
                         uu____5032 :: uu____5033  in
                       let uu____5037 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5025 uu____5037  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5058 =
                           let uu____5063 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5063)
                            in
                         let uu____5064 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5058 uu____5064  in
                       let uu____5067 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5067 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5099 =
                             let uu____5100 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5100  in
                           if uu____5099
                           then no_reify eff_name
                           else
                             (let uu____5106 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5107 =
                                let uu____5110 =
                                  let uu____5111 =
                                    let uu____5126 =
                                      let uu____5129 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5130 =
                                        let uu____5133 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5133]  in
                                      uu____5129 :: uu____5130  in
                                    (repr, uu____5126)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5111  in
                                FStar_Syntax_Syntax.mk uu____5110  in
                              uu____5107 FStar_Pervasives_Native.None
                                uu____5106)
                        in
                     let uu____5139 =
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
                               let uu____5192 =
                                 let uu____5195 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 FStar_Pervasives_Native.fst uu____5195  in
                               FStar_Syntax_Subst.subst uu____5192 lift_wp
                             else lift_wp  in
                           let uu____5209 =
                             check_and_gen env1 lift_wp1 expected_k  in
                           (lift, uu____5209)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let lift1 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5235 =
                                 let uu____5238 =
                                   FStar_Syntax_Subst.univ_var_opening what
                                    in
                                 FStar_Pervasives_Native.fst uu____5238  in
                               FStar_Syntax_Subst.subst uu____5235 lift
                             else lift  in
                           ((let uu____5253 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5253
                             then
                               let uu____5254 =
                                 FStar_Syntax_Print.term_to_string lift1  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5254
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5257 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift1
                                in
                             match uu____5257 with
                             | (lift2,comp,uu____5272) ->
                                 let uu____5273 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift2
                                    in
                                 (match uu____5273 with
                                  | (uu____5286,lift_wp,lift_elab) ->
                                      let uu____5289 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5290 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5139 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___78_5331 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___78_5331.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___78_5331.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___78_5331.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___78_5331.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___78_5331.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___78_5331.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___78_5331.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___78_5331.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___78_5331.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___78_5331.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___78_5331.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___78_5331.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___78_5331.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___78_5331.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___78_5331.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___78_5331.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___78_5331.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___78_5331.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___78_5331.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___78_5331.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___78_5331.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___78_5331.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___78_5331.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___78_5331.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___78_5331.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___78_5331.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___78_5331.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___78_5331.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___78_5331.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___78_5331.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___78_5331.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___78_5331.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___78_5331.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___78_5331.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5337,lift1)
                                ->
                                let uu____5349 =
                                  let uu____5356 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5356
                                   in
                                (match uu____5349 with
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
                                         let uu____5380 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5381 =
                                           let uu____5384 =
                                             let uu____5385 =
                                               let uu____5400 =
                                                 let uu____5403 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5404 =
                                                   let uu____5407 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5407]  in
                                                 uu____5403 :: uu____5404  in
                                               (lift_wp1, uu____5400)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5385
                                              in
                                           FStar_Syntax_Syntax.mk uu____5384
                                            in
                                         uu____5381
                                           FStar_Pervasives_Native.None
                                           uu____5380
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5416 =
                                         let uu____5423 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5424 =
                                           let uu____5427 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5428 =
                                             let uu____5431 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5431]  in
                                           uu____5427 :: uu____5428  in
                                         uu____5423 :: uu____5424  in
                                       let uu____5432 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5416
                                         uu____5432
                                        in
                                     let uu____5435 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5435 with
                                      | (expected_k2,uu____5445,uu____5446)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift2))
                             in
                          let sub2 =
                            let uu___79_5449 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___79_5449.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___79_5449.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___80_5451 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___80_5451.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___80_5451.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___80_5451.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___80_5451.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let uu____5466 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (uvs, tps, c)
             else
               (let uu____5480 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____5480 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____5507 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____5507 c  in
                    (uvs1, tps1, c1))
              in
           (match uu____5466 with
            | (uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____5528 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____5528 with
                 | (tps2,c2) ->
                     let uu____5543 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____5543 with
                      | (tps3,env3,us) ->
                          let uu____5561 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____5561 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____5582 =
                                   let uu____5583 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____5583
                                    in
                                 match uu____5582 with
                                 | (uvs2,t) ->
                                     let uu____5598 =
                                       let uu____5611 =
                                         let uu____5616 =
                                           let uu____5617 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____5617.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____5616)  in
                                       match uu____5611 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____5632,c5)) -> ([], c5)
                                       | (uu____5672,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____5699 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____5598 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____5743 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____5743 with
                                              | (uu____5748,t1) ->
                                                  let uu____5750 =
                                                    let uu____5755 =
                                                      let uu____5756 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____5757 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____5758 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____5756 uu____5757
                                                        uu____5758
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____5755)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5750 r)
                                           else ();
                                           (let se1 =
                                              let uu___81_5761 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___81_5761.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___81_5761.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___81_5761.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___81_5761.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], []))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5778,uu____5779,uu____5780) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5784  ->
                   match uu___56_5784 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5785 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5790,uu____5791) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5799  ->
                   match uu___56_5799 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5800 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____5810 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____5810
             then
               let uu____5811 =
                 let uu____5816 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5816)
                  in
               FStar_Errors.raise_error uu____5811 r
             else ());
            (let uu____5818 =
               if uvs = []
               then
                 let uu____5819 =
                   let uu____5820 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____5820  in
                 check_and_gen env2 t uu____5819
               else
                 (let uu____5826 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____5826 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5834 =
                          let uu____5835 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____5835  in
                        tc_check_trivial_guard env2 t1 uu____5834  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____5841 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____5841))
                in
             match uu____5818 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___82_5857 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___82_5857.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___82_5857.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___82_5857.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___82_5857.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5867 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____5867 with
            | (uu____5880,phi1) ->
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
           let uu____5890 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____5890 with
            | (e1,c,g1) ->
                let uu____5908 =
                  let uu____5915 =
                    let uu____5918 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____5918  in
                  let uu____5919 =
                    let uu____5924 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____5924)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5915 uu____5919
                   in
                (match uu____5908 with
                 | (e2,uu____5934,g) ->
                     ((let uu____5937 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5937);
                      (let se1 =
                         let uu___83_5939 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5939.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5939.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5939.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5939.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5990 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____5990
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5998 =
                      let uu____6003 =
                        let uu____6004 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6005 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6006 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6004 uu____6005 uu____6006
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6003)
                       in
                    FStar_Errors.raise_error uu____5998 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6032 =
                   let uu____6033 = FStar_Syntax_Subst.compress def  in
                   uu____6033.FStar_Syntax_Syntax.n  in
                 match uu____6032 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6043,uu____6044)
                     -> binders
                 | uu____6065 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6075;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6153) -> val_bs1
                     | (uu____6176,[]) -> val_bs1
                     | ((body_bv,uu____6200)::bt,(val_bv,aqual)::vt) ->
                         let uu____6237 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6253) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___84_6255 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___85_6258 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___85_6258.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___84_6255.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___84_6255.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6237
                      in
                   let uu____6259 =
                     let uu____6262 =
                       let uu____6263 =
                         let uu____6276 = rename_binders1 def_bs val_bs  in
                         (uu____6276, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6263  in
                     FStar_Syntax_Syntax.mk uu____6262  in
                   uu____6259 FStar_Pervasives_Native.None r1
               | uu____6294 -> typ1  in
             let uu___86_6295 = lb  in
             let uu____6296 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___86_6295.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___86_6295.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6296;
               FStar_Syntax_Syntax.lbeff =
                 (uu___86_6295.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___86_6295.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___86_6295.FStar_Syntax_Syntax.lbattrs)
             }  in
           let uu____6299 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6350  ->
                     fun lb  ->
                       match uu____6350 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6392 =
                             let uu____6403 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6403 with
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
                                   | uu____6488 ->
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
                                  (let uu____6531 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6531, quals_opt1)))
                              in
                           (match uu____6392 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6299 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6625 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6629  ->
                                match uu___57_6629 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6630 -> false))
                         in
                      if uu____6625
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6640 =
                    let uu____6643 =
                      let uu____6644 =
                        let uu____6657 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6657)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6644  in
                    FStar_Syntax_Syntax.mk uu____6643  in
                  uu____6640 FStar_Pervasives_Native.None r  in
                let uu____6675 =
                  let uu____6686 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___87_6695 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___87_6695.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___87_6695.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___87_6695.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___87_6695.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___87_6695.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___87_6695.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___87_6695.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___87_6695.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___87_6695.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___87_6695.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___87_6695.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___87_6695.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___87_6695.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___87_6695.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___87_6695.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___87_6695.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___87_6695.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___87_6695.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___87_6695.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___87_6695.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___87_6695.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___87_6695.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___87_6695.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___87_6695.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___87_6695.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___87_6695.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___87_6695.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___87_6695.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___87_6695.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___87_6695.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___87_6695.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___87_6695.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___87_6695.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6686 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6708;
                       FStar_Syntax_Syntax.vars = uu____6709;_},uu____6710,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6739 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6739)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6757,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6762 -> quals  in
                      ((let uu___88_6770 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___88_6770.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___88_6770.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___88_6770.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6779 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6675 with
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
                      (let uu____6828 = log env2  in
                       if uu____6828
                       then
                         let uu____6829 =
                           let uu____6830 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6845 =
                                         let uu____6854 =
                                           let uu____6855 =
                                             let uu____6858 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____6858.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____6855.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6854
                                          in
                                       match uu____6845 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6865 -> false  in
                                     if should_log
                                     then
                                       let uu____6874 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____6875 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6874 uu____6875
                                     else ""))
                              in
                           FStar_All.pipe_right uu____6830
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____6829
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6906 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____6906 with
                              | (bs1,c1) ->
                                  let uu____6913 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____6913
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6925 =
                                            let uu____6926 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____6926.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6925 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6951 =
                                                 let uu____6952 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____6952.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6951 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6962 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6962
                                                       in
                                                    let uu____6963 =
                                                      let uu____6964 =
                                                        let uu____6965 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6965 args
                                                         in
                                                      uu____6964
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6963 u
                                                | uu____6968 -> c1)
                                           | uu____6969 -> c1)
                                      | uu____6970 -> c1  in
                                    let uu___89_6971 = t1  in
                                    let uu____6972 =
                                      let uu____6973 =
                                        let uu____6986 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____6986)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6973
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6972;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___89_6971.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___89_6971.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____7010 =
                               let uu____7011 = FStar_Syntax_Subst.compress h
                                  in
                               uu____7011.FStar_Syntax_Syntax.n  in
                             (match uu____7010 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____7021 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____7021
                                     in
                                  let uu____7022 =
                                    let uu____7023 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7023
                                      args
                                     in
                                  uu____7022 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____7026 -> t1)
                         | uu____7027 -> t1  in
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
                           let uu____7055 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____7055
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____7072 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x)
                                   in
                                (uu____7072, (FStar_Pervasives_Native.snd x)))
                             bs
                            in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.tac_effect_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange
                            in
                         let unit_binder =
                           let uu____7103 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____7103
                            in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp))
                            in
                         let uu___90_7110 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___91_7122 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___91_7122.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___91_7122.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___91_7122.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___91_7122.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___91_7122.FStar_Syntax_Syntax.lbattrs)
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___90_7110.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___90_7110.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___90_7110.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___90_7110.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7139 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____7139 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp
                                     in
                                  let uu____7173 =
                                    let uu____7174 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____7174.FStar_Syntax_Syntax.n  in
                                  (match uu____7173 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h
                                          in
                                       let tac_lid =
                                         let uu____7207 =
                                           let uu____7210 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname
                                              in
                                           uu____7210.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____7207.FStar_Syntax_Syntax.v  in
                                       let assm_lid =
                                         let uu____7212 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                            in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7212
                                          in
                                       let uu____7213 =
                                         get_tactic_fv env2 assm_lid h1  in
                                       (match uu____7213 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7223 =
                                              let uu____7224 =
                                                let uu____7225 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7225
                                                 in
                                              Prims.op_Negation uu____7224
                                               in
                                            if uu____7223
                                            then
                                              ((let uu____7255 =
                                                  let uu____7256 =
                                                    FStar_Syntax_Util.is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule
                                                     in
                                                  Prims.op_Negation
                                                    uu____7256
                                                   in
                                                if uu____7255
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
                                                          module_name
                                                          added_modules)
                                                   then
                                                     FStar_ST.op_Colon_Equals
                                                       user_tactics_modules
                                                       (FStar_List.append
                                                          added_modules
                                                          [module_name])
                                                   else ())
                                                else ());
                                               (let uu____7309 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid
                                                   in
                                                if uu____7309
                                                then
                                                  let se_assm =
                                                    reified_tactic_decl
                                                      assm_lid hd1
                                                     in
                                                  let se_refl =
                                                    reflected_tactic_decl
                                                      (FStar_Pervasives_Native.fst
                                                         lbs1) hd1 bs
                                                      assm_lid comp
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    (se_assm, se_refl)
                                                else
                                                  FStar_Pervasives_Native.None))
                                            else FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7338 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7343 -> FStar_Pervasives_Native.None  in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7365 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____7365
                             then
                               let uu____7366 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____7367 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7366 uu____7367
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
             (fun uu___58_7418  ->
                match uu___58_7418 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7419 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7425) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7431 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7440 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7445 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7470 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7494) ->
          let uu____7503 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7503
          then
            let for_export_bundle se1 uu____7534 =
              match uu____7534 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7573,uu____7574) ->
                       let dec =
                         let uu___92_7584 = se1  in
                         let uu____7585 =
                           let uu____7586 =
                             let uu____7593 =
                               let uu____7596 =
                                 FStar_Syntax_Syntax.mk_Total t  in
                               FStar_Syntax_Util.arrow bs uu____7596  in
                             (l, us, uu____7593)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7586  in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7585;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7584.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7584.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7584.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7608,uu____7609,uu____7610) ->
                       let dec =
                         let uu___93_7616 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7616.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7616.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7616.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ((dec :: out), (l :: hidden1))
                   | uu____7621 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7643,uu____7644,uu____7645) ->
          let uu____7646 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7646 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7667 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____7667
          then
            ([(let uu___94_7683 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___94_7683.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___94_7683.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___94_7683.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7685 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_7689  ->
                       match uu___59_7689 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7690 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7695 -> true
                       | uu____7696 -> false))
                in
             if uu____7685 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7714 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7719 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7724 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7729 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7734 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7752) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____7769 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____7769
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
          let uu____7800 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
          if uu____7800
          then
            let uu____7809 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___95_7822 = se  in
                      let uu____7823 =
                        let uu____7824 =
                          let uu____7831 =
                            let uu____7832 =
                              let uu____7835 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname
                                 in
                              uu____7835.FStar_Syntax_Syntax.fv_name  in
                            uu____7832.FStar_Syntax_Syntax.v  in
                          (uu____7831, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp))
                           in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7824  in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7823;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___95_7822.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___95_7822.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___95_7822.FStar_Syntax_Syntax.sigattrs)
                      }))
               in
            (uu____7809, hidden)
          else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7855 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7872 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7887) ->
          let env1 =
            let uu____7891 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7891 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7893 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7894 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7904 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7904) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7905,uu____7906,uu____7907) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7911  ->
                  match uu___60_7911 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7912 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7913,uu____7914) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7922  ->
                  match uu___60_7922 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7923 -> false))
          -> env
      | uu____7924 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7984 se =
        match uu____7984 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____8037 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____8037
              then
                let uu____8038 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8038
              else ());
             (let uu____8040 = tc_decl env1 se  in
              match uu____8040 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____8090 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____8090
                             then
                               let uu____8091 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____8091
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
                    (let uu____8114 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____8114
                     then
                       let uu____8115 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8121 =
                                  let uu____8122 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____8122 "\n"  in
                                Prims.strcat s uu____8121) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____8115
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8127 =
                       let uu____8136 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____8136
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____8171 se1 =
                            match uu____8171 with
                            | (exports1,hidden1) ->
                                let uu____8199 = for_export hidden1 se1  in
                                (match uu____8199 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____8127 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___96_8278 = s  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___96_8278.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___96_8278.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___96_8278.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___96_8278.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1
                            in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____8356 = acc  in
        match uu____8356 with
        | (uu____8391,uu____8392,env1,uu____8394) ->
            let uu____8407 =
              FStar_Util.record_time
                (fun uu____8453  -> process_one_decl acc se)
               in
            (match uu____8407 with
             | (r,ms_elapsed) ->
                 ((let uu____8517 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____8517
                   then
                     let uu____8518 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____8519 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8518 uu____8519
                   else ());
                  r))
         in
      let uu____8521 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____8521 with
      | (ses1,exports,env1,uu____8569) ->
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
          let uu___97_8600 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___97_8600.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___97_8600.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___97_8600.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___97_8600.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___97_8600.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___97_8600.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___97_8600.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___97_8600.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___97_8600.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___97_8600.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___97_8600.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___97_8600.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___97_8600.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___97_8600.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___97_8600.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___97_8600.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___97_8600.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___97_8600.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___97_8600.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___97_8600.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___97_8600.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___97_8600.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___97_8600.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___97_8600.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___97_8600.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___97_8600.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___97_8600.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___97_8600.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___97_8600.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___97_8600.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___97_8600.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___97_8600.FStar_TypeChecker_Env.dep_graph)
          }  in
        let check_term lid univs1 t =
          let uu____8611 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____8611 with
          | (univs2,t1) ->
              ((let uu____8619 =
                  let uu____8620 =
                    let uu____8623 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____8623  in
                  FStar_All.pipe_left uu____8620
                    (FStar_Options.Other "Exports")
                   in
                if uu____8619
                then
                  let uu____8624 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____8625 =
                    let uu____8626 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____8626
                      (FStar_String.concat ", ")
                     in
                  let uu____8635 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8624 uu____8625 uu____8635
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____8638 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____8638 FStar_Pervasives.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____8662 =
             let uu____8663 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____8664 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8663 uu____8664
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8662);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8671) ->
              let uu____8680 =
                let uu____8681 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8681  in
              if uu____8680
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8691,uu____8692) ->
              let t =
                let uu____8704 =
                  let uu____8707 =
                    let uu____8708 =
                      let uu____8721 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____8721)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____8708  in
                  FStar_Syntax_Syntax.mk uu____8707  in
                uu____8704 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8728,uu____8729,uu____8730) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8738 =
                let uu____8739 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8739  in
              if uu____8738 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8743,lbs),uu____8745) ->
              let uu____8760 =
                let uu____8761 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8761  in
              if uu____8760
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
              let uu____8780 =
                let uu____8781 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____8781  in
              if uu____8780
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8788 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8789 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8796 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8797 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8798 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8799 -> ()  in
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
             | FStar_Syntax_Syntax.Projector (l,uu____8876) -> true
             | uu____8877 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____8896 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____8927 ->
                   let uu____8928 =
                     let uu____8931 =
                       let uu____8932 =
                         let uu____8945 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____8945)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____8932  in
                     FStar_Syntax_Syntax.mk uu____8931  in
                   uu____8928 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____8953,uu____8954) ->
            let s1 =
              let uu___98_8964 = s  in
              let uu____8965 =
                let uu____8966 =
                  let uu____8973 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____8973)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____8966  in
              let uu____8974 =
                let uu____8977 =
                  let uu____8980 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____8980  in
                FStar_Syntax_Syntax.Assumption :: uu____8977  in
              {
                FStar_Syntax_Syntax.sigel = uu____8965;
                FStar_Syntax_Syntax.sigrng =
                  (uu___98_8964.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____8974;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___98_8964.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___98_8964.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____8983 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____8997 =
        match uu____8997 with
        | (uvs,t) ->
            let uu___99_9004 = s  in
            let uu____9005 =
              let uu____9008 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____9008  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___99_9004.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____9005;
              FStar_Syntax_Syntax.sigmeta =
                (uu___99_9004.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___99_9004.FStar_Syntax_Syntax.sigattrs)
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____9020 -> failwith "Impossible!"  in
        let c_opt =
          let uu____9024 = FStar_Syntax_Util.is_unit t  in
          if uu____9024
          then
            let uu____9027 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____9027
          else
            (let uu____9029 =
               let uu____9030 = FStar_Syntax_Subst.compress t  in
               uu____9030.FStar_Syntax_Syntax.n  in
             match uu____9029 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____9035,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____9055 -> FStar_Pervasives_Native.None)
           in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must  in
           ((FStar_Syntax_Util.is_pure_or_ghost_comp c) ||
              (let uu____9063 = comp_effect_name1 c  in
               FStar_TypeChecker_Util.is_reifiable env uu____9063))
             &&
             (let uu____9065 =
                let uu____9066 =
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_result  in
                FStar_All.pipe_right uu____9066 FStar_Syntax_Util.is_unit  in
              Prims.op_Negation uu____9065))
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9081 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9100 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9148,uu____9149,uu____9150,uu____9151,uu____9152)
                         ->
                         ((let uu____9162 =
                             let uu____9165 =
                               FStar_ST.op_Bang abstract_inductive_tycons  in
                             lid :: uu____9165  in
                           FStar_ST.op_Colon_Equals abstract_inductive_tycons
                             uu____9162);
                          (let uu____9258 = vals_of_abstract_inductive s1  in
                           FStar_List.append uu____9258 sigelts1))
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9262,uu____9263,uu____9264,uu____9265,uu____9266)
                         ->
                         ((let uu____9272 =
                             let uu____9275 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9275  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9272);
                          sigelts1)
                     | uu____9368 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9375 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9375
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____9381 =
                   let uu___100_9382 = s  in
                   let uu____9383 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___100_9382.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___100_9382.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9383;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___100_9382.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___100_9382.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9381])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9393 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9393
            then []
            else
              (let uu____9397 = lbs  in
               match uu____9397 with
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
                       (fun uu____9453  ->
                          match uu____9453 with
                          | (uu____9460,t) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs
                      in
                   let vals =
                     FStar_List.map2
                       (fun lid  ->
                          fun uu____9478  ->
                            match uu____9478 with
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
                          (fun uu____9498  ->
                             match uu____9498 with
                             | (uu____9505,t) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs
                         in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid,uu____9518,uu____9519) ->
            let is_haseq = FStar_TypeChecker_Util.is_haseq_lid lid  in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____9524 = FStar_ST.op_Bang abstract_inductive_tycons
                   in
                FStar_List.existsML
                  (fun l  ->
                     let uu____9575 =
                       FStar_TypeChecker_Util.get_haseq_axiom_lid l  in
                     FStar_Ident.lid_equals lid uu____9575) uu____9524
                 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____9578 =
                   let uu___101_9579 = s  in
                   let uu____9580 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___101_9579.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___101_9579.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____9580;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___101_9579.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___101_9579.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 [uu____9578]
               else [])
            else
              (let uu____9585 =
                 let uu___102_9586 = s  in
                 let uu____9587 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___102_9586.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___102_9586.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9587;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___102_9586.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___102_9586.FStar_Syntax_Syntax.sigattrs)
                 }  in
               [uu____9585])
        | FStar_Syntax_Syntax.Sig_new_effect uu____9590 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9591 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9592 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9593 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9606 -> [s]  in
      let uu___103_9607 = m  in
      let uu____9608 =
        let uu____9609 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9609  in
      {
        FStar_Syntax_Syntax.name = (uu___103_9607.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9608;
        FStar_Syntax_Syntax.exports =
          (uu___103_9607.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      (let uu____9623 = FStar_ToSyntax_Env.pop ()  in
       FStar_All.pipe_right uu____9623 FStar_Pervasives.ignore);
      (let en = FStar_TypeChecker_Env.pop env msg  in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
       en)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv  in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___104_9634 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___104_9634.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___104_9634.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___104_9634.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___104_9634.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___104_9634.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___104_9634.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___104_9634.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___104_9634.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___104_9634.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___104_9634.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___104_9634.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___104_9634.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___104_9634.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___104_9634.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___104_9634.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___104_9634.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___104_9634.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___104_9634.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___104_9634.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___104_9634.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___104_9634.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___104_9634.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___104_9634.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___104_9634.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___104_9634.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___104_9634.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___104_9634.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___104_9634.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___104_9634.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___104_9634.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___104_9634.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___104_9634.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___104_9634.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___104_9634.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____9655 = FStar_Options.debug_any ()  in
       if uu____9655
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
         let uu___105_9660 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___105_9660.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___105_9660.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___105_9660.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___105_9660.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___105_9660.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___105_9660.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___105_9660.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___105_9660.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___105_9660.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___105_9660.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___105_9660.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___105_9660.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___105_9660.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___105_9660.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___105_9660.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___105_9660.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___105_9660.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___105_9660.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___105_9660.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___105_9660.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___105_9660.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___105_9660.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___105_9660.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___105_9660.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___105_9660.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___105_9660.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___105_9660.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___105_9660.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___105_9660.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___105_9660.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___105_9660.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___105_9660.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___105_9660.FStar_TypeChecker_Env.dep_graph)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____9662 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____9662 with
       | (ses,exports,env3) ->
           ((let uu___106_9695 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___106_9695.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___106_9695.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___106_9695.FStar_Syntax_Syntax.is_interface)
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
        let uu____9717 = tc_decls env decls  in
        match uu____9717 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___107_9748 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___107_9748.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___107_9748.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___107_9748.FStar_Syntax_Syntax.is_interface)
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
          let uu___108_9793 = env0  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___108_9793.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___108_9793.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___108_9793.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___108_9793.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___108_9793.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___108_9793.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___108_9793.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___108_9793.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___108_9793.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___108_9793.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___108_9793.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___108_9793.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___108_9793.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___108_9793.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___108_9793.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___108_9793.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___108_9793.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___108_9793.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes =
              (uu___108_9793.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___108_9793.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___108_9793.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___108_9793.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___108_9793.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___108_9793.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___108_9793.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___108_9793.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___108_9793.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___108_9793.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___108_9793.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___108_9793.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___108_9793.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___108_9793.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___108_9793.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___108_9793.FStar_TypeChecker_Env.dep_graph)
          }
        else env0  in
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let env02 = push_context env01 msg  in
      let uu____9797 = tc_partial_modul env02 m  in
      match uu____9797 with
      | (modul,non_private_decls,env) ->
          let uu____9821 =
            finish_partial_modul false env modul non_private_decls  in
          (match uu____9821 with
           | (m1,m_opt,env1) ->
               (m1, m_opt,
                 (let uu___109_9848 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___109_9848.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___109_9848.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___109_9848.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___109_9848.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___109_9848.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___109_9848.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___109_9848.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___109_9848.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___109_9848.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___109_9848.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___109_9848.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___109_9848.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___109_9848.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___109_9848.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___109_9848.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___109_9848.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___109_9848.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___109_9848.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = lax_mode;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___109_9848.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___109_9848.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___109_9848.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___109_9848.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___109_9848.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___109_9848.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___109_9848.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___109_9848.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___109_9848.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___109_9848.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth =
                      (uu___109_9848.FStar_TypeChecker_Env.synth);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___109_9848.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___109_9848.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___109_9848.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___109_9848.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___109_9848.FStar_TypeChecker_Env.dep_graph)
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
          let uu____9863 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
             in
          if uu____9863
          then
            let en0 =
              pop_context en
                (Prims.strcat "Ending modul "
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            let en01 =
              let uu___110_9874 = en0  in
              let uu____9875 =
                let uu____9888 =
                  FStar_All.pipe_right
                    en.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                (uu____9888, FStar_Pervasives_Native.None)  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___110_9874.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___110_9874.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___110_9874.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___110_9874.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___110_9874.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___110_9874.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___110_9874.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___110_9874.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___110_9874.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___110_9874.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___110_9874.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___110_9874.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___110_9874.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___110_9874.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___110_9874.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___110_9874.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___110_9874.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___110_9874.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___110_9874.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___110_9874.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___110_9874.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___110_9874.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___110_9874.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___110_9874.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___110_9874.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___110_9874.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___110_9874.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index = uu____9875;
                FStar_TypeChecker_Env.proof_ns =
                  (uu___110_9874.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___110_9874.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___110_9874.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___110_9874.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___110_9874.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___110_9874.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___110_9874.FStar_TypeChecker_Env.dep_graph)
              }  in
            ((let uu____9926 =
                let uu____9927 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____9927  in
              if uu____9926
              then
                let uu____9928 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____9928 FStar_Pervasives.ignore
              else ());
             (let modul_iface = extract_interface en01 m  in
              (let uu____9932 =
                 let uu____9933 =
                   FStar_Options.dump_module
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____9933
                 then
                   let uu____9934 =
                     let uu____9935 = FStar_Syntax_Print.modul_to_string m
                        in
                     Prims.strcat uu____9935 "\n"  in
                   Prims.strcat "\nfrom: " uu____9934
                 else ""  in
               let uu____9937 =
                 let uu____9938 =
                   FStar_Options.dump_module
                     (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____9938
                 then
                   let uu____9939 =
                     let uu____9940 =
                       FStar_Syntax_Print.modul_to_string modul_iface  in
                     Prims.strcat uu____9940 "\n"  in
                   Prims.strcat "\nto: " uu____9939
                 else ""  in
               FStar_Util.print3
                 "Extracting and type checking module %s interface%s%s\n"
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____9932
                 uu____9937);
              (let env0 =
                 let uu___111_9943 = en01  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___111_9943.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___111_9943.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___111_9943.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___111_9943.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___111_9943.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___111_9943.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___111_9943.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___111_9943.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___111_9943.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___111_9943.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___111_9943.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___111_9943.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___111_9943.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___111_9943.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___111_9943.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___111_9943.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface = true;
                   FStar_TypeChecker_Env.admit =
                     (uu___111_9943.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___111_9943.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___111_9943.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___111_9943.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___111_9943.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___111_9943.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___111_9943.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___111_9943.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___111_9943.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___111_9943.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___111_9943.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___111_9943.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___111_9943.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___111_9943.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___111_9943.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___111_9943.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___111_9943.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___111_9943.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let uu____9944 = tc_modul en01 modul_iface  in
               match uu____9944 with
               | (modul_iface1,must_be_none,env) ->
                   if must_be_none <> FStar_Pervasives_Native.None
                   then
                     failwith
                       "Impossible! Expected the second component to be None"
                   else (m, (FStar_Pervasives_Native.Some modul_iface1), env))))
          else
            (let modul =
               let uu____9991 = FStar_Options.use_extracted_interfaces ()  in
               if uu____9991
               then
                 let uu___112_9992 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___112_9992.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___112_9992.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___112_9992.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___113_9994 = m  in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___113_9994.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___113_9994.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___113_9994.FStar_Syntax_Syntax.is_interface)
                  })
                in
             let env = FStar_TypeChecker_Env.finish_module en modul  in
             (let uu____9997 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst
                 in
              FStar_All.pipe_right uu____9997 FStar_Util.smap_clear);
             (let uu____10025 =
                ((let uu____10028 = FStar_Options.lax ()  in
                  Prims.op_Negation uu____10028) &&
                   (let uu____10030 =
                      FStar_Options.use_extracted_interfaces ()  in
                    Prims.op_Negation uu____10030))
                  && (Prims.op_Negation loading_from_cache)
                 in
              if uu____10025 then check_exports env modul exports else ());
             (let uu____10033 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 in
              FStar_All.pipe_right uu____10033 FStar_Pervasives.ignore);
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____10037 =
                let uu____10038 = FStar_Options.interactive ()  in
                Prims.op_Negation uu____10038  in
              if uu____10037
              then
                let uu____10039 = FStar_Options.restore_cmd_line_options true
                   in
                FStar_All.pipe_right uu____10039 FStar_Pervasives.ignore
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
        let uu____10051 =
          let uu____10052 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____10052  in
        push_context env uu____10051  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____10071 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____10092 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports  in
      match uu____10092 with | (uu____10101,uu____10102,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun m  ->
      (let uu____10123 = FStar_Options.debug_any ()  in
       if uu____10123
       then
         let uu____10124 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____10124
       else ());
      (let env1 =
         let uu___114_10128 = env  in
         let uu____10129 =
           let uu____10130 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____10130  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___114_10128.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___114_10128.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___114_10128.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___114_10128.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___114_10128.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___114_10128.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___114_10128.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___114_10128.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___114_10128.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___114_10128.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___114_10128.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___114_10128.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___114_10128.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___114_10128.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___114_10128.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___114_10128.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___114_10128.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___114_10128.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____10129;
           FStar_TypeChecker_Env.lax_universes =
             (uu___114_10128.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___114_10128.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___114_10128.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___114_10128.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___114_10128.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___114_10128.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___114_10128.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___114_10128.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___114_10128.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___114_10128.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___114_10128.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___114_10128.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___114_10128.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___114_10128.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___114_10128.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___114_10128.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____10131 = tc_modul env1 m  in
       match uu____10131 with
       | (m1,m_iface_opt,env2) ->
           ((let uu____10156 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____10156
             then
               let uu____10157 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____10157
             else ());
            (let uu____10160 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____10160
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
                       let uu____10191 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____10191 with
                       | (univnames1,e) ->
                           let uu___115_10198 = lb  in
                           let uu____10199 =
                             let uu____10202 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____10202 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___115_10198.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___115_10198.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___115_10198.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___115_10198.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____10199;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___115_10198.FStar_Syntax_Syntax.lbattrs)
                           }
                        in
                     let uu___116_10203 = se  in
                     let uu____10204 =
                       let uu____10205 =
                         let uu____10212 =
                           let uu____10219 = FStar_List.map update lbs  in
                           (b, uu____10219)  in
                         (uu____10212, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____10205  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____10204;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___116_10203.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___116_10203.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___116_10203.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___116_10203.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____10232 -> se  in
               let normalized_module =
                 let uu___117_10234 = m1  in
                 let uu____10235 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___117_10234.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____10235;
                   FStar_Syntax_Syntax.exports =
                     (uu___117_10234.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___117_10234.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____10236 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____10236
             else ());
            (m1, m_iface_opt, env2)))
  