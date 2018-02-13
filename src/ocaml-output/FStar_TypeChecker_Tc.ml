open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for ()  in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____12 l  in
          let uu___56_13 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___56_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___56_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___56_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___56_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___56_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___56_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___56_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___56_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___56_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___56_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___56_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___56_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___56_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___56_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___56_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___56_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___56_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___56_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___56_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___56_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___56_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___56_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___56_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___56_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___56_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___56_13.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___56_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___56_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___56_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___56_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___56_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___56_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___56_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___56_13.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env  in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l  in
          let uu___57_29 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___57_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___57_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___57_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___57_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___57_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___57_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___57_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___57_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___57_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___57_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___57_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___57_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___57_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___57_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___57_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___57_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___57_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___57_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___57_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___57_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___57_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___57_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___57_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___57_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___57_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___57_29.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___57_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___57_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___57_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___57_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___57_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___57_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___57_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___57_29.FStar_TypeChecker_Env.dep_graph)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____38 =
         let uu____39 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39  in
       Prims.op_Negation uu____38)
  
let get_tactic_fv :
  'Auu____44 .
    'Auu____44 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____60) ->
            let uu____65 =
              let uu____66 = FStar_Syntax_Subst.compress h'  in
              uu____66.FStar_Syntax_Syntax.n  in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____72 -> FStar_Pervasives_Native.None)
        | uu____73 -> FStar_Pervasives_Native.None
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____80 =
        let uu____83 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____83  in
      match uu____80 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____96 -> false
    else false
  
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
        let uu____193 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____193 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____214 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____214
         then
           let uu____215 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____215
         else ());
        (let uu____217 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____217 with
         | (t',uu____225,uu____226) ->
             ((let uu____228 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____228
               then
                 let uu____229 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____229
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
        let uu____240 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____240
  
let check_nogen :
  'Auu____245 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____245 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____265 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1
           in
        ([], uu____265)
  
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
        let fail uu____292 =
          let uu____293 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          FStar_Errors.raise_error uu____293 (FStar_Ident.range_of_lid m)  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____337)::(wp,uu____339)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____354 -> fail ())
        | uu____355 -> fail ()
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____362 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____362 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____388 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____388 t  in
          let open_univs_binders n_binders bs =
            let uu____398 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____398 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____406 =
            let uu____413 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____414 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____413 uu____414  in
          (match uu____406 with
           | (effect_params_un,signature_un,opening) ->
               let uu____424 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un
                  in
               (match uu____424 with
                | (effect_params,env,uu____433) ->
                    let uu____434 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un
                       in
                    (match uu____434 with
                     | (signature,uu____440) ->
                         let ed1 =
                           let uu___58_442 = ed  in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___58_442.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___58_442.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___58_442.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___58_442.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___58_442.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___58_442.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___58_442.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___58_442.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___58_442.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___58_442.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___58_442.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___58_442.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___58_442.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___58_442.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___58_442.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___58_442.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___58_442.FStar_Syntax_Syntax.actions)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____458 ->
                               let op uu____480 =
                                 match uu____480 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____500 =
                                       let uu____501 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____510 =
                                         open_univs (n_effect_params + n_us)
                                           t
                                          in
                                       FStar_Syntax_Subst.subst uu____501
                                         uu____510
                                        in
                                     (us, uu____500)
                                  in
                               let uu___59_523 = ed1  in
                               let uu____524 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____525 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____526 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else  in
                               let uu____527 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp  in
                               let uu____528 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____529 =
                                 op ed1.FStar_Syntax_Syntax.close_wp  in
                               let uu____530 =
                                 op ed1.FStar_Syntax_Syntax.assert_p  in
                               let uu____531 =
                                 op ed1.FStar_Syntax_Syntax.assume_p  in
                               let uu____532 =
                                 op ed1.FStar_Syntax_Syntax.null_wp  in
                               let uu____533 =
                                 op ed1.FStar_Syntax_Syntax.trivial  in
                               let uu____534 =
                                 let uu____535 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____535  in
                               let uu____546 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____547 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____548 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___60_556 = a  in
                                      let uu____557 =
                                        let uu____558 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd uu____558
                                         in
                                      let uu____569 =
                                        let uu____570 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd uu____570
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___60_556.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___60_556.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___60_556.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___60_556.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____557;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____569
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___59_523.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___59_523.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___59_523.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___59_523.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____524;
                                 FStar_Syntax_Syntax.bind_wp = uu____525;
                                 FStar_Syntax_Syntax.if_then_else = uu____526;
                                 FStar_Syntax_Syntax.ite_wp = uu____527;
                                 FStar_Syntax_Syntax.stronger = uu____528;
                                 FStar_Syntax_Syntax.close_wp = uu____529;
                                 FStar_Syntax_Syntax.assert_p = uu____530;
                                 FStar_Syntax_Syntax.assume_p = uu____531;
                                 FStar_Syntax_Syntax.null_wp = uu____532;
                                 FStar_Syntax_Syntax.trivial = uu____533;
                                 FStar_Syntax_Syntax.repr = uu____534;
                                 FStar_Syntax_Syntax.return_repr = uu____546;
                                 FStar_Syntax_Syntax.bind_repr = uu____547;
                                 FStar_Syntax_Syntax.actions = uu____548
                               }
                            in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____607 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t
                                in
                             FStar_Errors.raise_error uu____607
                               (FStar_Ident.range_of_lid mname)
                              in
                           let uu____618 =
                             let uu____619 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____619.FStar_Syntax_Syntax.n  in
                           match uu____618 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____654)::(wp,uu____656)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____671 -> fail signature1)
                           | uu____672 -> fail signature1  in
                         let uu____673 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____673 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____695 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____702 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un
                                       in
                                    (match uu____702 with
                                     | (signature1,uu____714) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____715 ->
                                    let uu____718 =
                                      let uu____723 =
                                        let uu____724 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____724)  in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____723
                                       in
                                    (match uu____718 with
                                     | (uu____733,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env1 =
                                let uu____736 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env uu____736
                                 in
                              ((let uu____738 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____738
                                then
                                  let uu____739 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____740 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____741 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____742 =
                                    let uu____743 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____743
                                     in
                                  let uu____744 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____739 uu____740 uu____741 uu____742
                                    uu____744
                                else ());
                               (let check_and_gen' env2 uu____760 k =
                                  match uu____760 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____774::uu____775 ->
                                           let uu____778 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____778 with
                                            | (us1,t1) ->
                                                let uu____787 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____787 with
                                                 | (us2,t2) ->
                                                     let uu____794 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k
                                                        in
                                                     let uu____795 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____795))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____800 =
                                      let uu____807 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____808 =
                                        let uu____811 =
                                          let uu____812 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____812
                                           in
                                        [uu____811]  in
                                      uu____807 :: uu____808  in
                                    let uu____813 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____800
                                      uu____813
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____817 = fresh_effect_signature ()
                                     in
                                  match uu____817 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____833 =
                                          let uu____840 =
                                            let uu____841 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____841
                                             in
                                          [uu____840]  in
                                        let uu____842 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____833
                                          uu____842
                                         in
                                      let expected_k =
                                        let uu____848 =
                                          let uu____855 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____856 =
                                            let uu____859 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____860 =
                                              let uu____863 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____864 =
                                                let uu____867 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____868 =
                                                  let uu____871 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____871]  in
                                                uu____867 :: uu____868  in
                                              uu____863 :: uu____864  in
                                            uu____859 :: uu____860  in
                                          uu____855 :: uu____856  in
                                        let uu____872 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____848
                                          uu____872
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let if_then_else1 =
                                  let p =
                                    let uu____877 =
                                      let uu____878 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____878
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____877
                                     in
                                  let expected_k =
                                    let uu____890 =
                                      let uu____897 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____898 =
                                        let uu____901 =
                                          FStar_Syntax_Syntax.mk_binder p  in
                                        let uu____902 =
                                          let uu____905 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          let uu____906 =
                                            let uu____909 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____909]  in
                                          uu____905 :: uu____906  in
                                        uu____901 :: uu____902  in
                                      uu____897 :: uu____898  in
                                    let uu____910 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____890
                                      uu____910
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k
                                   in
                                let ite_wp =
                                  let expected_k =
                                    let uu____917 =
                                      let uu____924 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____925 =
                                        let uu____928 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a
                                           in
                                        [uu____928]  in
                                      uu____924 :: uu____925  in
                                    let uu____929 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____917
                                      uu____929
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k
                                   in
                                let stronger =
                                  let uu____933 = FStar_Syntax_Util.type_u ()
                                     in
                                  match uu____933 with
                                  | (t,uu____939) ->
                                      let expected_k =
                                        let uu____943 =
                                          let uu____950 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____951 =
                                            let uu____954 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            let uu____955 =
                                              let uu____958 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____958]  in
                                            uu____954 :: uu____955  in
                                          uu____950 :: uu____951  in
                                        let uu____959 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Util.arrow uu____943
                                          uu____959
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k
                                   in
                                let close_wp =
                                  let b =
                                    let uu____964 =
                                      let uu____965 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____965
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____964
                                     in
                                  let b_wp_a =
                                    let uu____977 =
                                      let uu____984 =
                                        let uu____985 =
                                          FStar_Syntax_Syntax.bv_to_name b
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____985
                                         in
                                      [uu____984]  in
                                    let uu____986 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____977
                                      uu____986
                                     in
                                  let expected_k =
                                    let uu____992 =
                                      let uu____999 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1000 =
                                        let uu____1003 =
                                          FStar_Syntax_Syntax.mk_binder b  in
                                        let uu____1004 =
                                          let uu____1007 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a
                                             in
                                          [uu____1007]  in
                                        uu____1003 :: uu____1004  in
                                      uu____999 :: uu____1000  in
                                    let uu____1008 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____992
                                      uu____1008
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k
                                   in
                                let assert_p =
                                  let expected_k =
                                    let uu____1015 =
                                      let uu____1022 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1023 =
                                        let uu____1026 =
                                          let uu____1027 =
                                            let uu____1028 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1028
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1027
                                           in
                                        let uu____1037 =
                                          let uu____1040 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1040]  in
                                        uu____1026 :: uu____1037  in
                                      uu____1022 :: uu____1023  in
                                    let uu____1041 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1015
                                      uu____1041
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k
                                   in
                                let assume_p =
                                  let expected_k =
                                    let uu____1048 =
                                      let uu____1055 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____1056 =
                                        let uu____1059 =
                                          let uu____1060 =
                                            let uu____1061 =
                                              FStar_Syntax_Util.type_u ()  in
                                            FStar_All.pipe_right uu____1061
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1060
                                           in
                                        let uu____1070 =
                                          let uu____1073 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a
                                             in
                                          [uu____1073]  in
                                        uu____1059 :: uu____1070  in
                                      uu____1055 :: uu____1056  in
                                    let uu____1074 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1048
                                      uu____1074
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k
                                   in
                                let null_wp =
                                  let expected_k =
                                    let uu____1081 =
                                      let uu____1088 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      [uu____1088]  in
                                    let uu____1089 =
                                      FStar_Syntax_Syntax.mk_Total wp_a  in
                                    FStar_Syntax_Util.arrow uu____1081
                                      uu____1089
                                     in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k
                                   in
                                let trivial_wp =
                                  let uu____1093 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____1093 with
                                  | (t,uu____1099) ->
                                      let expected_k =
                                        let uu____1103 =
                                          let uu____1110 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____1111 =
                                            let uu____1114 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____1114]  in
                                          uu____1110 :: uu____1111  in
                                        let uu____1115 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____1103
                                          uu____1115
                                         in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k
                                   in
                                let uu____1118 =
                                  let uu____1129 =
                                    let uu____1130 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr
                                       in
                                    uu____1130.FStar_Syntax_Syntax.n  in
                                  match uu____1129 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1145 ->
                                      let repr =
                                        let uu____1147 =
                                          FStar_Syntax_Util.type_u ()  in
                                        match uu____1147 with
                                        | (t,uu____1153) ->
                                            let expected_k =
                                              let uu____1157 =
                                                let uu____1164 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1165 =
                                                  let uu____1168 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____1168]  in
                                                uu____1164 :: uu____1165  in
                                              let uu____1169 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1157 uu____1169
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
                                        let uu____1182 =
                                          let uu____1185 =
                                            let uu____1186 =
                                              let uu____1201 =
                                                let uu____1204 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____1205 =
                                                  let uu____1208 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp
                                                     in
                                                  [uu____1208]  in
                                                uu____1204 :: uu____1205  in
                                              (repr1, uu____1201)  in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1186
                                             in
                                          FStar_Syntax_Syntax.mk uu____1185
                                           in
                                        uu____1182
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      let mk_repr a1 wp =
                                        let uu____1223 =
                                          FStar_Syntax_Syntax.bv_to_name a1
                                           in
                                        mk_repr' uu____1223 wp  in
                                      let destruct_repr t =
                                        let uu____1236 =
                                          let uu____1237 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____1237.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1236 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1248,(t1,uu____1250)::
                                             (wp,uu____1252)::[])
                                            -> (t1, wp)
                                        | uu____1295 ->
                                            failwith "Unexpected repr type"
                                         in
                                      let bind_repr =
                                        let r =
                                          let uu____1306 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____1306
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____1307 =
                                          fresh_effect_signature ()  in
                                        match uu____1307 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1323 =
                                                let uu____1330 =
                                                  let uu____1331 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1331
                                                   in
                                                [uu____1330]  in
                                              let uu____1332 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1323 uu____1332
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
                                              let uu____1338 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1338
                                               in
                                            let wp_g_x =
                                              let uu____1342 =
                                                let uu____1343 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g
                                                   in
                                                let uu____1344 =
                                                  let uu____1345 =
                                                    let uu____1346 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1346
                                                     in
                                                  [uu____1345]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1343 uu____1344
                                                 in
                                              uu____1342
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            let res =
                                              let wp =
                                                let uu____1355 =
                                                  let uu____1356 =
                                                    let uu____1357 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1357
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____1366 =
                                                    let uu____1367 =
                                                      let uu____1370 =
                                                        let uu____1373 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        let uu____1374 =
                                                          let uu____1377 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          let uu____1378 =
                                                            let uu____1381 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            let uu____1382 =
                                                              let uu____1385
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g
                                                                 in
                                                              [uu____1385]
                                                               in
                                                            uu____1381 ::
                                                              uu____1382
                                                             in
                                                          uu____1377 ::
                                                            uu____1378
                                                           in
                                                        uu____1373 ::
                                                          uu____1374
                                                         in
                                                      r :: uu____1370  in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1367
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1356 uu____1366
                                                   in
                                                uu____1355
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr b wp  in
                                            let expected_k =
                                              let uu____1391 =
                                                let uu____1398 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____1399 =
                                                  let uu____1402 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____1403 =
                                                    let uu____1406 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f
                                                       in
                                                    let uu____1407 =
                                                      let uu____1410 =
                                                        let uu____1411 =
                                                          let uu____1412 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f
                                                             in
                                                          mk_repr a
                                                            uu____1412
                                                           in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1411
                                                         in
                                                      let uu____1413 =
                                                        let uu____1416 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g
                                                           in
                                                        let uu____1417 =
                                                          let uu____1420 =
                                                            let uu____1421 =
                                                              let uu____1422
                                                                =
                                                                let uu____1429
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a
                                                                   in
                                                                [uu____1429]
                                                                 in
                                                              let uu____1430
                                                                =
                                                                let uu____1433
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1433
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1422
                                                                uu____1430
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1421
                                                             in
                                                          [uu____1420]  in
                                                        uu____1416 ::
                                                          uu____1417
                                                         in
                                                      uu____1410 ::
                                                        uu____1413
                                                       in
                                                    uu____1406 :: uu____1407
                                                     in
                                                  uu____1402 :: uu____1403
                                                   in
                                                uu____1398 :: uu____1399  in
                                              let uu____1434 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____1391 uu____1434
                                               in
                                            let uu____1437 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k
                                               in
                                            (match uu____1437 with
                                             | (expected_k1,uu____1445,uu____1446)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                    in
                                                 let env3 =
                                                   let uu___61_1451 = env2
                                                      in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___61_1451.FStar_TypeChecker_Env.dep_graph)
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
                                          let uu____1461 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1461
                                           in
                                        let res =
                                          let wp =
                                            let uu____1468 =
                                              let uu____1469 =
                                                let uu____1470 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp
                                                   in
                                                FStar_All.pipe_right
                                                  uu____1470
                                                  FStar_Pervasives_Native.snd
                                                 in
                                              let uu____1479 =
                                                let uu____1480 =
                                                  let uu____1483 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let uu____1484 =
                                                    let uu____1487 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a
                                                       in
                                                    [uu____1487]  in
                                                  uu____1483 :: uu____1484
                                                   in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1480
                                                 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1469 uu____1479
                                               in
                                            uu____1468
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          mk_repr a wp  in
                                        let expected_k =
                                          let uu____1493 =
                                            let uu____1500 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____1501 =
                                              let uu____1504 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a
                                                 in
                                              [uu____1504]  in
                                            uu____1500 :: uu____1501  in
                                          let uu____1505 =
                                            FStar_Syntax_Syntax.mk_Total res
                                             in
                                          FStar_Syntax_Util.arrow uu____1493
                                            uu____1505
                                           in
                                        let uu____1508 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k
                                           in
                                        match uu____1508 with
                                        | (expected_k1,uu____1522,uu____1523)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let uu____1527 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1
                                               in
                                            (match uu____1527 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1548 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos))
                                         in
                                      let actions =
                                        let check_action act =
                                          let uu____1573 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ
                                             in
                                          match uu____1573 with
                                          | (act_typ,uu____1581,g_t) ->
                                              let env' =
                                                let uu___62_1584 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ
                                                   in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___62_1584.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___62_1584.FStar_TypeChecker_Env.dep_graph)
                                                }  in
                                              ((let uu____1586 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____1586
                                                then
                                                  let uu____1587 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn
                                                     in
                                                  let uu____1588 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ
                                                     in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1587 uu____1588
                                                else ());
                                               (let uu____1590 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn
                                                   in
                                                match uu____1590 with
                                                | (act_defn,uu____1598,g_a)
                                                    ->
                                                    let act_defn1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant]
                                                        env1 act_defn
                                                       in
                                                    let act_typ1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant;
                                                        FStar_TypeChecker_Normalize.Eager_unfolding;
                                                        FStar_TypeChecker_Normalize.Beta]
                                                        env1 act_typ
                                                       in
                                                    let uu____1602 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1
                                                         in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1630 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c
                                                             in
                                                          (match uu____1630
                                                           with
                                                           | (bs1,uu____1640)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let k =
                                                                 let uu____1647
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1647
                                                                  in
                                                               let uu____1650
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k
                                                                  in
                                                               (match uu____1650
                                                                with
                                                                | (k1,uu____1662,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1664 ->
                                                          let uu____1665 =
                                                            let uu____1670 =
                                                              let uu____1671
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2
                                                                 in
                                                              let uu____1672
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2
                                                                 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1671
                                                                uu____1672
                                                               in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1670)
                                                             in
                                                          FStar_Errors.raise_error
                                                            uu____1665
                                                            act_defn1.FStar_Syntax_Syntax.pos
                                                       in
                                                    (match uu____1602 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k
                                                            in
                                                         ((let uu____1681 =
                                                             let uu____1682 =
                                                               let uu____1683
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g
                                                                  in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1683
                                                                in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1682
                                                              in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1681);
                                                          (let act_typ2 =
                                                             let uu____1687 =
                                                               let uu____1688
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k
                                                                  in
                                                               uu____1688.FStar_Syntax_Syntax.n
                                                                in
                                                             match uu____1687
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1711
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____1711
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1720
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____1720
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1742
                                                                    =
                                                                    let uu____1743
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1743]
                                                                     in
                                                                    let uu____1744
                                                                    =
                                                                    let uu____1753
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1753]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1742;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1744;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1754
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1754))
                                                             | uu____1757 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)"
                                                              in
                                                           let uu____1760 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1
                                                              in
                                                           match uu____1760
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ3 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ2
                                                                  in
                                                               let act_typ4 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ3
                                                                  in
                                                               let uu___63_1769
                                                                 = act  in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___63_1769.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___63_1769.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___63_1769.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ4
                                                               })))))
                                           in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action)
                                         in
                                      (repr, bind_repr, return_repr, actions)
                                   in
                                match uu____1118 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1793 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1793
                                       in
                                    let uu____1796 =
                                      let uu____1803 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0
                                         in
                                      match uu____1803 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1824 ->
                                               let uu____1827 =
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
                                               if uu____1827
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1841 =
                                                    let uu____1846 =
                                                      let uu____1847 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names)
                                                         in
                                                      let uu____1848 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs)
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1847 uu____1848
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1846)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____1841
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                       in
                                    (match uu____1796 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1862 =
                                             let uu____1867 =
                                               let uu____1868 =
                                                 FStar_Syntax_Subst.compress
                                                   t
                                                  in
                                               uu____1868.FStar_Syntax_Syntax.n
                                                in
                                             (effect_params, uu____1867)  in
                                           match uu____1862 with
                                           | ([],uu____1871) -> t
                                           | (uu____1882,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1883,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1901 ->
                                               failwith
                                                 "Impossible : t is an arrow"
                                            in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1914 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts
                                                in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1914
                                              in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1)
                                              in
                                           (let uu____1919 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1921 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1)
                                                     in
                                                  Prims.op_Negation
                                                    uu____1921))
                                                && (m <> n1)
                                               in
                                            if uu____1919
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic"
                                                 in
                                              let err_msg =
                                                let uu____1937 =
                                                  FStar_Util.string_of_int m
                                                   in
                                                let uu____1944 =
                                                  FStar_Util.string_of_int n1
                                                   in
                                                let uu____1945 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1
                                                   in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1937 uu____1944
                                                  uu____1945
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1  in
                                         let close_action act =
                                           let uu____1953 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn))
                                              in
                                           match uu____1953 with
                                           | (univs2,defn) ->
                                               let uu____1960 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               (match uu____1960 with
                                                | (univs',typ) ->
                                                    let uu___64_1970 = act
                                                       in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___64_1970.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___64_1970.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___64_1970.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    })
                                            in
                                         let ed3 =
                                           let uu___65_1975 = ed2  in
                                           let uu____1976 =
                                             close1 (Prims.parse_int "0")
                                               return_wp
                                              in
                                           let uu____1977 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp
                                              in
                                           let uu____1978 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1
                                              in
                                           let uu____1979 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp
                                              in
                                           let uu____1980 =
                                             close1 (Prims.parse_int "0")
                                               stronger
                                              in
                                           let uu____1981 =
                                             close1 (Prims.parse_int "1")
                                               close_wp
                                              in
                                           let uu____1982 =
                                             close1 (Prims.parse_int "0")
                                               assert_p
                                              in
                                           let uu____1983 =
                                             close1 (Prims.parse_int "0")
                                               assume_p
                                              in
                                           let uu____1984 =
                                             close1 (Prims.parse_int "0")
                                               null_wp
                                              in
                                           let uu____1985 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp
                                              in
                                           let uu____1986 =
                                             let uu____1987 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr)
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____1987
                                              in
                                           let uu____1998 =
                                             close1 (Prims.parse_int "0")
                                               return_repr
                                              in
                                           let uu____1999 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr
                                              in
                                           let uu____2000 =
                                             FStar_List.map close_action
                                               actions
                                              in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___65_1975.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___65_1975.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1976;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1977;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1978;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1979;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1980;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1981;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1982;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1983;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1984;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1985;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1986;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1998;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1999;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2000
                                           }  in
                                         ((let uu____2004 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED"))
                                              in
                                           if uu____2004
                                           then
                                             let uu____2005 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3
                                                in
                                             FStar_Util.print_string
                                               uu____2005
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
      let uu____2023 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____2023 with
      | (effect_binders_un,signature_un) ->
          let uu____2040 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____2040 with
           | (effect_binders,env1,uu____2059) ->
               let uu____2060 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____2060 with
                | (signature,uu____2076) ->
                    let raise_error1 a uu____2087 =
                      match uu____2087 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2113  ->
                           match uu____2113 with
                           | (bv,qual) ->
                               let uu____2124 =
                                 let uu___66_2125 = bv  in
                                 let uu____2126 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___66_2125.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___66_2125.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2126
                                 }  in
                               (uu____2124, qual)) effect_binders
                       in
                    let uu____2129 =
                      let uu____2136 =
                        let uu____2137 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____2137.FStar_Syntax_Syntax.n  in
                      Obj.magic
                        (match uu____2136 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2147)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2169 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature")))
                       in
                    (match uu____2129 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2187 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____2187
                           then
                             let uu____2188 =
                               let uu____2191 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____2191  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2188
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____2225 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____2225 with
                           | (t2,comp,uu____2238) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____2245 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____2245 with
                          | (repr,_comp) ->
                              ((let uu____2267 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2267
                                then
                                  let uu____2268 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2268
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
                                  let uu____2274 =
                                    let uu____2275 =
                                      let uu____2276 =
                                        let uu____2291 =
                                          let uu____2298 =
                                            let uu____2303 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____2304 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____2303, uu____2304)  in
                                          [uu____2298]  in
                                        (wp_type1, uu____2291)  in
                                      FStar_Syntax_Syntax.Tm_app uu____2276
                                       in
                                    mk1 uu____2275  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2274
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____2329 =
                                      let uu____2334 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____2334)  in
                                    let uu____2335 =
                                      let uu____2342 =
                                        let uu____2343 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____2343
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____2342]  in
                                    uu____2329 :: uu____2335  in
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
                                  let uu____2406 = item  in
                                  match uu____2406 with
                                  | (u_item,item1) ->
                                      let uu____2427 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____2427 with
                                       | (item2,item_comp) ->
                                           ((let uu____2443 =
                                               let uu____2444 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____2444
                                                in
                                             if uu____2443
                                             then
                                               let uu____2445 =
                                                 let uu____2450 =
                                                   let uu____2451 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____2452 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2451 uu____2452
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2450)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____2445
                                             else ());
                                            (let uu____2454 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____2454 with
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
                                let uu____2474 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____2474 with
                                | (dmff_env1,uu____2498,bind_wp,bind_elab) ->
                                    let uu____2501 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____2501 with
                                     | (dmff_env2,uu____2525,return_wp,return_elab)
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
                                           let uu____2532 =
                                             let uu____2533 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2533.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2532 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2577 =
                                                       let uu____2592 =
                                                         let uu____2597 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2597
                                                          in
                                                       match uu____2592 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2661 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity"
                                                        in
                                                     match uu____2577 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2700 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2
                                                              in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2700
                                                             [b11; b21]
                                                            in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2717 =
                                                               let uu____2718
                                                                 =
                                                                 let uu____2733
                                                                   =
                                                                   let uu____2740
                                                                    =
                                                                    let uu____2745
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____2746
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2745,
                                                                    uu____2746)
                                                                     in
                                                                   [uu____2740]
                                                                    in
                                                                 (wp_type1,
                                                                   uu____2733)
                                                                  in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2718
                                                                in
                                                             mk1 uu____2717
                                                              in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1
                                                            in
                                                         let uu____2761 =
                                                           let uu____2770 =
                                                             let uu____2771 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1
                                                                in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2771
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2770
                                                            in
                                                         (match uu____2761
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2790
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2792
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2  in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2792
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
                                                                    let uu____2798
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
                                                                    uu____2798
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
                                                                  let uu____2825
                                                                    =
                                                                    let uu____2826
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                    let uu____2827
                                                                    =
                                                                    let uu____2828
                                                                    =
                                                                    let uu____2835
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____2835,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____2828]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2826
                                                                    uu____2827
                                                                     in
                                                                  uu____2825
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                   in
                                                                let uu____2860
                                                                  =
                                                                  let uu____2861
                                                                    =
                                                                    let uu____2868
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                    [uu____2868]
                                                                     in
                                                                  b11 ::
                                                                    uu____2861
                                                                   in
                                                                let uu____2873
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what
                                                                   in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2860
                                                                  uu____2873
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2874 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let return_wp1 =
                                           let uu____2876 =
                                             let uu____2877 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2877.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2876 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2921 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2921
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2934 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return")))
                                            in
                                         let bind_wp1 =
                                           let uu____2936 =
                                             let uu____2937 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2937.FStar_Syntax_Syntax.n
                                              in
                                           Obj.magic
                                             (match uu____2936 with
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
                                                     let uu____2964 =
                                                       let uu____2965 =
                                                         let uu____2968 =
                                                           let uu____2969 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r)
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____2969
                                                            in
                                                         [uu____2968]  in
                                                       FStar_List.append
                                                         uu____2965 binders
                                                        in
                                                     FStar_Syntax_Util.abs
                                                       uu____2964 body what)
                                              | uu____2970 ->
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
                                             (let uu____2988 =
                                                let uu____2989 =
                                                  let uu____2990 =
                                                    let uu____3005 =
                                                      let uu____3006 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3006
                                                       in
                                                    (t, uu____3005)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2990
                                                   in
                                                mk1 uu____2989  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2988)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3036 = f a2  in
                                               [uu____3036]
                                           | x::xs ->
                                               let uu____3041 =
                                                 apply_last1 f xs  in
                                               x :: uu____3041
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
                                           let uu____3061 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____3061 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3091 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____3091
                                                 then
                                                   let uu____3092 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3092
                                                 else ());
                                                (let uu____3094 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3094))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3103 =
                                                 let uu____3108 = mk_lid name
                                                    in
                                                 let uu____3109 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3108 uu____3109
                                                  in
                                               (match uu____3103 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3113 =
                                                        let uu____3116 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____3116
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3113);
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
                                          (let uu____3317 =
                                             let uu____3320 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true"))
                                                in
                                             let uu____3321 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____3320 :: uu____3321  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3317);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            FStar_Options.push ();
                                            (let uu____3523 =
                                               let uu____3526 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true"))
                                                  in
                                               let uu____3527 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____3526 :: uu____3527  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3523);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             FStar_Options.pop ();
                                             (let uu____3726 =
                                                FStar_List.fold_left
                                                  (fun uu____3766  ->
                                                     fun action  ->
                                                       match uu____3766 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____3787 =
                                                             let uu____3794 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3794
                                                               params_un
                                                              in
                                                           (match uu____3787
                                                            with
                                                            | (action_params,env',uu____3803)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3823
                                                                     ->
                                                                    match uu____3823
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3834
                                                                    =
                                                                    let uu___67_3835
                                                                    = bv  in
                                                                    let uu____3836
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___67_3835.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___67_3835.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3836
                                                                    }  in
                                                                    (uu____3834,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____3840
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____3840
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
                                                                    uu____3870
                                                                    ->
                                                                    let uu____3871
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3871
                                                                     in
                                                                    ((
                                                                    let uu____3875
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3875
                                                                    then
                                                                    let uu____3876
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____3877
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____3878
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____3879
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3876
                                                                    uu____3877
                                                                    uu____3878
                                                                    uu____3879
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
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    let uu___68_3887
                                                                    = action
                                                                     in
                                                                    let uu____3888
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____3889
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___68_3887.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___68_3887.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___68_3887.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3888;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3889
                                                                    }  in
                                                                    uu____3886
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____3883))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____3726 with
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
                                                      let uu____3922 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____3923 =
                                                        let uu____3926 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____3926]  in
                                                      uu____3922 ::
                                                        uu____3923
                                                       in
                                                    let uu____3927 =
                                                      let uu____3928 =
                                                        let uu____3929 =
                                                          let uu____3930 =
                                                            let uu____3945 =
                                                              let uu____3952
                                                                =
                                                                let uu____3957
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____3958
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____3957,
                                                                  uu____3958)
                                                                 in
                                                              [uu____3952]
                                                               in
                                                            (repr,
                                                              uu____3945)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3930
                                                           in
                                                        mk1 uu____3929  in
                                                      let uu____3973 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3928
                                                        uu____3973
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3927
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____3976 =
                                                    let uu____3983 =
                                                      let uu____3984 =
                                                        let uu____3987 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3987
                                                         in
                                                      uu____3984.FStar_Syntax_Syntax.n
                                                       in
                                                    Obj.magic
                                                      (match uu____3983 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3997)
                                                           ->
                                                           Obj.repr
                                                             (let uu____4026
                                                                =
                                                                let uu____4043
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1
                                                                   in
                                                                match uu____4043
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____4101
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                 in
                                                              match uu____4026
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____4151
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4155
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____4155
                                                                     in
                                                                    uu____4152.FStar_Syntax_Syntax.n
                                                                     in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____4151
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4180
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    match uu____4180
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____4193
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4218
                                                                     ->
                                                                    match uu____4218
                                                                    with
                                                                    | 
                                                                    (bv,uu____4224)
                                                                    ->
                                                                    let uu____4225
                                                                    =
                                                                    let uu____4226
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4226
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4225
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____4193
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
                                                                    let uu____4290
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4290
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4295
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4303
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4303
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____4308
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____4311
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____4308,
                                                                    uu____4311)))
                                                                    | 
                                                                    uu____4318
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4319
                                                                    =
                                                                    let uu____4324
                                                                    =
                                                                    let uu____4325
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4325
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4324)
                                                                     in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4319)))
                                                       | uu____4326 ->
                                                           Obj.repr
                                                             (let uu____4327
                                                                =
                                                                let uu____4332
                                                                  =
                                                                  let uu____4333
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                     in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4333
                                                                   in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4332)
                                                                 in
                                                              raise_error1 ()
                                                                uu____4327))
                                                     in
                                                  (match uu____3976 with
                                                   | (pre,post) ->
                                                       ((let uu____4351 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____4353 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____4355 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___69_4357 =
                                                             ed  in
                                                           let uu____4358 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____4359 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____4360 =
                                                             let uu____4361 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____4361)
                                                              in
                                                           let uu____4368 =
                                                             let uu____4369 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____4369)
                                                              in
                                                           let uu____4376 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____4377 =
                                                             let uu____4378 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____4378)
                                                              in
                                                           let uu____4385 =
                                                             let uu____4386 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____4386)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4358;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4359;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4360;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4368;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___69_4357.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4376;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4377;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4385;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____4393 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____4393
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4411
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____4411
                                                               then
                                                                 let uu____4412
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____4412
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
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4427
                                                                    =
                                                                    let uu____4436
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____4436)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4427
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
                                                                    uu____4424;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____4451
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4451
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____4453
                                                                 =
                                                                 let uu____4456
                                                                   =
                                                                   let uu____4459
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____4459
                                                                    in
                                                                 FStar_List.append
                                                                   uu____4456
                                                                   sigelts'
                                                                  in
                                                               (uu____4453,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____4568 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4568 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4601 = FStar_List.hd ses  in
            uu____4601.FStar_Syntax_Syntax.sigrng  in
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
           | uu____4606 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4611,uu____4612);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4614;
               FStar_Syntax_Syntax.sigattrs = uu____4615;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4619);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4621;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4622;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4626);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4628;
                 FStar_Syntax_Syntax.sigattrs = uu____4629;_}::[]
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
                 let uu____4694 =
                   let uu____4697 =
                     let uu____4698 =
                       let uu____4705 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____4705, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____4698  in
                   FStar_Syntax_Syntax.mk uu____4697  in
                 uu____4694 FStar_Pervasives_Native.None r1  in
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
                   let uu____4723 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4723
                    in
                 let hd1 =
                   let uu____4725 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4725
                    in
                 let tl1 =
                   let uu____4727 =
                     let uu____4728 =
                       let uu____4731 =
                         let uu____4732 =
                           let uu____4739 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____4739, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____4732  in
                       FStar_Syntax_Syntax.mk uu____4731  in
                     uu____4728 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4727
                    in
                 let res =
                   let uu____4748 =
                     let uu____4751 =
                       let uu____4752 =
                         let uu____4759 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4759,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____4752  in
                     FStar_Syntax_Syntax.mk uu____4751  in
                   uu____4748 FStar_Pervasives_Native.None r2  in
                 let uu____4765 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4765
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
               let uu____4804 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4804;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4809 ->
               let err_msg =
                 let uu____4813 =
                   let uu____4814 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____4814  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4813
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
            let uu____4839 = FStar_Syntax_Util.type_u ()  in
            match uu____4839 with
            | (k,uu____4845) ->
                let phi1 =
                  let uu____4847 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____4847
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4849 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1  in
                  match uu____4849 with
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
          let uu____4891 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids
             in
          match uu____4891 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4924 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas
                   in
                FStar_All.pipe_right uu____4924 FStar_List.flatten  in
              ((let uu____4938 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____4938
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
                          let uu____4949 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4959,uu____4960,uu____4961,uu____4962,uu____4963)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4972 -> failwith "Impossible!"  in
                          match uu____4949 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4983 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4987,uu____4988,uu____4989,uu____4990,uu____4991)
                        -> lid
                    | uu____5000 -> failwith "Impossible"  in
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
                  let uu____5018 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq
                     in
                  if uu____5018
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
                     let uu____5041 =
                       let uu____5044 =
                         let uu____5045 =
                           FStar_TypeChecker_Env.get_range env1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____5045;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       uu____5044 :: ses1  in
                     (uu____5041, data_ops_ses))
                   in
                (let uu____5055 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5089 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____5114 ->
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
           let uu____5166 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____5166 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____5204 = cps_and_elaborate env1 ne  in
           (match uu____5204 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___70_5241 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___70_5241.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___70_5241.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___70_5241.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___70_5241.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___71_5243 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___71_5243.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___71_5243.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___71_5243.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___71_5243.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 =
             let uu___72_5251 = se  in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___72_5251.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___72_5251.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___72_5251.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___72_5251.FStar_Syntax_Syntax.sigattrs)
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
           let uu____5259 =
             let uu____5266 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5266
              in
           (match uu____5259 with
            | (a,wp_a_src) ->
                let uu____5281 =
                  let uu____5288 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5288
                   in
                (match uu____5281 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5304 =
                         let uu____5307 =
                           let uu____5308 =
                             let uu____5315 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____5315)  in
                           FStar_Syntax_Syntax.NT uu____5308  in
                         [uu____5307]  in
                       FStar_Syntax_Subst.subst uu____5304 wp_b_tgt  in
                     let expected_k =
                       let uu____5319 =
                         let uu____5326 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____5327 =
                           let uu____5330 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____5330]  in
                         uu____5326 :: uu____5327  in
                       let uu____5331 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____5319 uu____5331  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5352 =
                           let uu____5357 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5357)
                            in
                         let uu____5358 =
                           FStar_TypeChecker_Env.get_range env1  in
                         FStar_Errors.raise_error uu____5352 uu____5358  in
                       let uu____5361 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____5361 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____5393 =
                             let uu____5394 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____5394  in
                           if uu____5393
                           then no_reify eff_name
                           else
                             (let uu____5400 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____5401 =
                                let uu____5404 =
                                  let uu____5405 =
                                    let uu____5420 =
                                      let uu____5423 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____5424 =
                                        let uu____5427 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____5427]  in
                                      uu____5423 :: uu____5424  in
                                    (repr, uu____5420)  in
                                  FStar_Syntax_Syntax.Tm_app uu____5405  in
                                FStar_Syntax_Syntax.mk uu____5404  in
                              uu____5401 FStar_Pervasives_Native.None
                                uu____5400)
                        in
                     let uu____5433 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5461,lift_wp)) ->
                           let uu____5485 =
                             check_and_gen env1 lift_wp expected_k  in
                           (lift, uu____5485)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5511 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED")
                                in
                             if uu____5511
                             then
                               let uu____5512 =
                                 FStar_Syntax_Print.term_to_string lift  in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5512
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange)
                                in
                             let uu____5515 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift  in
                             match uu____5515 with
                             | (lift1,comp,uu____5530) ->
                                 let uu____5531 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1
                                    in
                                 (match uu____5531 with
                                  | (uu____5544,lift_wp,lift_elab) ->
                                      let uu____5547 =
                                        recheck_debug "lift-wp" env1 lift_wp
                                         in
                                      let uu____5548 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab
                                         in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp)))))
                        in
                     (match uu____5433 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___73_5589 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___73_5589.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___73_5589.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___73_5589.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___73_5589.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___73_5589.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___73_5589.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___73_5589.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___73_5589.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___73_5589.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___73_5589.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___73_5589.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___73_5589.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___73_5589.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___73_5589.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___73_5589.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___73_5589.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___73_5589.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___73_5589.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___73_5589.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___73_5589.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___73_5589.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___73_5589.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___73_5589.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___73_5589.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___73_5589.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___73_5589.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___73_5589.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___73_5589.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___73_5589.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___73_5589.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___73_5589.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___73_5589.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___73_5589.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___73_5589.FStar_TypeChecker_Env.dep_graph)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5595,lift1)
                                ->
                                let uu____5607 =
                                  let uu____5614 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source
                                     in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5614
                                   in
                                (match uu____5607 with
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
                                         let uu____5638 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____5639 =
                                           let uu____5642 =
                                             let uu____5643 =
                                               let uu____5658 =
                                                 let uu____5661 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____5662 =
                                                   let uu____5665 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____5665]  in
                                                 uu____5661 :: uu____5662  in
                                               (lift_wp1, uu____5658)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5643
                                              in
                                           FStar_Syntax_Syntax.mk uu____5642
                                            in
                                         uu____5639
                                           FStar_Pervasives_Native.None
                                           uu____5638
                                          in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a
                                        in
                                     let expected_k1 =
                                       let uu____5674 =
                                         let uu____5681 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____5682 =
                                           let uu____5685 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____5686 =
                                             let uu____5689 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____5689]  in
                                           uu____5685 :: uu____5686  in
                                         uu____5681 :: uu____5682  in
                                       let uu____5690 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____5674
                                         uu____5690
                                        in
                                     let uu____5693 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____5693 with
                                      | (expected_k2,uu____5703,uu____5704)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2
                                             in
                                          FStar_Pervasives_Native.Some lift2))
                             in
                          let sub2 =
                            let uu___74_5707 = sub1  in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___74_5707.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___74_5707.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            }  in
                          let se1 =
                            let uu___75_5709 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___75_5709.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___75_5709.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___75_5709.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___75_5709.FStar_Syntax_Syntax.sigattrs)
                            }  in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____5728 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____5728 with
            | (tps1,c1) ->
                let uu____5743 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____5743 with
                 | (tps2,env3,us) ->
                     let uu____5761 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____5761 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____5782 =
                              let uu____5783 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5783
                               in
                            match uu____5782 with
                            | (uvs1,t) ->
                                let uu____5798 =
                                  let uu____5811 =
                                    let uu____5816 =
                                      let uu____5817 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____5817.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____5816)  in
                                  match uu____5811 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5832,c4)) -> ([], c4)
                                  | (uu____5872,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5899 ->
                                      failwith "Impossible (t is an arrow)"
                                   in
                                (match uu____5798 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5943 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____5943 with
                                         | (uu____5948,t1) ->
                                             let uu____5950 =
                                               let uu____5955 =
                                                 let uu____5956 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     lid
                                                    in
                                                 let uu____5957 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.length uvs1)
                                                     FStar_Util.string_of_int
                                                    in
                                                 let uu____5958 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 FStar_Util.format3
                                                   "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                   uu____5956 uu____5957
                                                   uu____5958
                                                  in
                                               (FStar_Errors.Fatal_TooManyUniverse,
                                                 uu____5955)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5950 r)
                                      else ();
                                      (let se1 =
                                         let uu___76_5961 = se  in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags1));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___76_5961.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___76_5961.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___76_5961.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___76_5961.FStar_Syntax_Syntax.sigattrs)
                                         }  in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5978,uu____5979,uu____5980) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___53_5984  ->
                   match uu___53_5984 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5985 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5990,uu____5991) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___53_5999  ->
                   match uu___53_5999 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____6000 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           ((let uu____6010 = FStar_TypeChecker_Env.lid_exists env2 lid  in
             if uu____6010
             then
               let uu____6011 =
                 let uu____6016 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid)
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____6016)
                  in
               FStar_Errors.raise_error uu____6011 r
             else ());
            (let uu____6018 =
               if uvs = []
               then
                 let uu____6019 =
                   let uu____6020 = FStar_Syntax_Util.type_u ()  in
                   FStar_Pervasives_Native.fst uu____6020  in
                 check_and_gen env2 t uu____6019
               else
                 (let uu____6026 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____6026 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____6034 =
                          let uu____6035 = FStar_Syntax_Util.type_u ()  in
                          FStar_Pervasives_Native.fst uu____6035  in
                        tc_check_trivial_guard env2 t1 uu____6034  in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2
                         in
                      let uu____6041 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                      (uvs1, uu____6041))
                in
             match uu____6018 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___77_6057 = se  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___77_6057.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___77_6057.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___77_6057.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___77_6057.FStar_Syntax_Syntax.sigattrs)
                   }  in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____6067 = FStar_Syntax_Subst.open_univ_vars us phi  in
           (match uu____6067 with
            | (uu____6080,phi1) ->
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
           let uu____6090 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____6090 with
            | (e1,c,g1) ->
                let uu____6108 =
                  let uu____6115 =
                    let uu____6118 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____6118  in
                  let uu____6119 =
                    let uu____6124 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____6124)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____6115 uu____6119
                   in
                (match uu____6108 with
                 | (e2,uu____6134,g) ->
                     ((let uu____6137 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____6137);
                      (let se1 =
                         let uu___78_6139 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___78_6139.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___78_6139.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___78_6139.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___78_6139.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____6190 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____6190
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6198 =
                      let uu____6203 =
                        let uu____6204 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____6205 = FStar_Syntax_Print.quals_to_string q
                           in
                        let uu____6206 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6204 uu____6205 uu____6206
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6203)
                       in
                    FStar_Errors.raise_error uu____6198 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____6232 =
                   let uu____6233 = FStar_Syntax_Subst.compress def  in
                   uu____6233.FStar_Syntax_Syntax.n  in
                 match uu____6232 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6243,uu____6244)
                     -> binders
                 | uu____6265 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6275;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6353) -> val_bs1
                     | (uu____6376,[]) -> val_bs1
                     | ((body_bv,uu____6400)::bt,(val_bv,aqual)::vt) ->
                         let uu____6437 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6453) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___79_6455 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___80_6458 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___80_6458.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___79_6455.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___79_6455.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6437
                      in
                   let uu____6459 =
                     let uu____6462 =
                       let uu____6463 =
                         let uu____6476 = rename_binders1 def_bs val_bs  in
                         (uu____6476, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____6463  in
                     FStar_Syntax_Syntax.mk uu____6462  in
                   uu____6459 FStar_Pervasives_Native.None r1
               | uu____6494 -> typ1  in
             let uu___81_6495 = lb  in
             let uu____6496 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___81_6495.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___81_6495.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6496;
               FStar_Syntax_Syntax.lbeff =
                 (uu___81_6495.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___81_6495.FStar_Syntax_Syntax.lbdef)
             }  in
           let uu____6499 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6550  ->
                     fun lb  ->
                       match uu____6550 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____6592 =
                             let uu____6603 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____6603 with
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
                                   | uu____6688 ->
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
                                  (let uu____6731 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def)
                                      in
                                   (false, uu____6731, quals_opt1)))
                              in
                           (match uu____6592 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____6499 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6825 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___54_6829  ->
                                match uu___54_6829 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6830 -> false))
                         in
                      if uu____6825
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____6840 =
                    let uu____6843 =
                      let uu____6844 =
                        let uu____6857 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6857)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____6844  in
                    FStar_Syntax_Syntax.mk uu____6843  in
                  uu____6840 FStar_Pervasives_Native.None r  in
                let uu____6875 =
                  let uu____6886 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___82_6895 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___82_6895.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___82_6895.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___82_6895.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___82_6895.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___82_6895.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___82_6895.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___82_6895.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___82_6895.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___82_6895.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___82_6895.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___82_6895.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___82_6895.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___82_6895.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___82_6895.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___82_6895.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___82_6895.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___82_6895.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___82_6895.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___82_6895.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___82_6895.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___82_6895.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___82_6895.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___82_6895.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___82_6895.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___82_6895.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___82_6895.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___82_6895.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___82_6895.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___82_6895.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___82_6895.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___82_6895.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___82_6895.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___82_6895.FStar_TypeChecker_Env.dep_graph)
                       }) e
                     in
                  match uu____6886 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6908;
                       FStar_Syntax_Syntax.vars = uu____6909;_},uu____6910,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6939 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters)
                           in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6939)  in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6957,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6962 -> quals  in
                      ((let uu___83_6970 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___83_6970.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___83_6970.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___83_6970.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6979 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)"
                   in
                (match uu____6875 with
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
                      (let uu____7028 = log env2  in
                       if uu____7028
                       then
                         let uu____7029 =
                           let uu____7030 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____7045 =
                                         let uu____7054 =
                                           let uu____7055 =
                                             let uu____7058 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____7058.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____7055.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____7054
                                          in
                                       match uu____7045 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____7065 -> false  in
                                     if should_log
                                     then
                                       let uu____7074 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____7075 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____7074 uu____7075
                                     else ""))
                              in
                           FStar_All.pipe_right uu____7030
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____7029
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t  in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____7106 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____7106 with
                              | (bs1,c1) ->
                                  let uu____7113 =
                                    FStar_Syntax_Util.is_total_comp c1  in
                                  if uu____7113
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____7125 =
                                            let uu____7126 =
                                              FStar_Syntax_Subst.compress t'
                                               in
                                            uu____7126.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7125 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____7151 =
                                                 let uu____7152 =
                                                   FStar_Syntax_Subst.compress
                                                     h
                                                    in
                                                 uu____7152.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7151 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____7162 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____7162
                                                       in
                                                    let uu____7163 =
                                                      let uu____7164 =
                                                        let uu____7165 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u'
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7165 args
                                                         in
                                                      uu____7164
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____7163 u
                                                | uu____7168 -> c1)
                                           | uu____7169 -> c1)
                                      | uu____7170 -> c1  in
                                    let uu___84_7171 = t1  in
                                    let uu____7172 =
                                      let uu____7173 =
                                        let uu____7186 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c'
                                           in
                                        (bs1, uu____7186)  in
                                      FStar_Syntax_Syntax.Tm_arrow uu____7173
                                       in
                                    {
                                      FStar_Syntax_Syntax.n = uu____7172;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___84_7171.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___84_7171.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____7210 =
                               let uu____7211 = FStar_Syntax_Subst.compress h
                                  in
                               uu____7211.FStar_Syntax_Syntax.n  in
                             (match uu____7210 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____7221 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____7221
                                     in
                                  let uu____7222 =
                                    let uu____7223 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u'
                                       in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7223
                                      args
                                     in
                                  uu____7222 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____7226 -> t1)
                         | uu____7227 -> t1  in
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
                           let uu____7255 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____7255
                            in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____7272 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x)
                                   in
                                (uu____7272, (FStar_Pervasives_Native.snd x)))
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
                           let uu____7303 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____7303
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
                         let uu___85_7310 = se1  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___86_7322 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___86_7322.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___86_7322.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___86_7322.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___86_7322.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___85_7310.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___85_7310.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___85_7310.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___85_7310.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7339 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp
                                in
                             (match uu____7339 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp
                                     in
                                  let uu____7373 =
                                    let uu____7374 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____7374.FStar_Syntax_Syntax.n  in
                                  (match uu____7373 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h
                                          in
                                       let tac_lid =
                                         let uu____7407 =
                                           let uu____7410 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname
                                              in
                                           uu____7410.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____7407.FStar_Syntax_Syntax.v  in
                                       let assm_lid =
                                         let uu____7412 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                            in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7412
                                          in
                                       let uu____7413 =
                                         get_tactic_fv env2 assm_lid h1  in
                                       (match uu____7413 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7423 =
                                              let uu____7424 =
                                                let uu____7425 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7425
                                                 in
                                              Prims.op_Negation uu____7424
                                               in
                                            if uu____7423
                                            then
                                              ((let uu____7455 =
                                                  let uu____7456 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule
                                                     in
                                                  Prims.op_Negation
                                                    uu____7456
                                                   in
                                                if uu____7455
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
                                               (let uu____7509 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid
                                                   in
                                                if uu____7509
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
                                   | uu____7538 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7543 -> FStar_Pervasives_Native.None  in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7565 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics")
                                in
                             if uu____7565
                             then
                               let uu____7566 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm
                                  in
                               let uu____7567 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl
                                  in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7566 uu____7567
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7587 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7604 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7619) ->
          let env1 =
            let uu____7623 = FStar_Options.using_facts_from ()  in
            FStar_TypeChecker_Env.set_proof_ns uu____7623 env  in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7625 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7626 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7636 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                       in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7636) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7637,uu____7638,uu____7639) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___55_7643  ->
                  match uu___55_7643 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7644 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7645,uu____7646) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___55_7654  ->
                  match uu___55_7654 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7655 -> false))
          -> env
      | uu____7656 -> FStar_TypeChecker_Env.push_sigelt env se
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7696 se =
        match uu____7696 with
        | (ses1,env1) ->
            ((let uu____7723 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____7723
              then
                let uu____7724 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7724
              else ());
             (let uu____7726 = tc_decl env1 se  in
              match uu____7726 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7768 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF")
                                in
                             if uu____7768
                             then
                               let uu____7769 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7769
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
                    (let uu____7792 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____7792
                     then
                       let uu____7793 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7799 =
                                  let uu____7800 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____7800 "\n"  in
                                Prims.strcat s uu____7799) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____7793
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let ses'2 =
                       FStar_List.map
                         (fun s  ->
                            let uu___87_7811 = s  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (uu___87_7811.FStar_Syntax_Syntax.sigel);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___87_7811.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___87_7811.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___87_7811.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (se.FStar_Syntax_Syntax.sigattrs)
                            }) ses'1
                        in
                     (((FStar_List.rev_append ses'2 ses1), env2),
                       ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____7853 = acc  in
        match uu____7853 with
        | (uu____7872,env1) ->
            let uu____7878 =
              FStar_Util.record_time
                (fun uu____7908  -> process_one_decl acc se)
               in
            (match uu____7878 with
             | (r,ms_elapsed) ->
                 ((let uu____7948 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime")
                      in
                   if uu____7948
                   then
                     let uu____7949 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____7950 = FStar_Util.string_of_int ms_elapsed  in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____7949 uu____7950
                   else ());
                  r))
         in
      let uu____7952 =
        FStar_Util.fold_flatten process_one_decl_timed ([], env) ses  in
      match uu____7952 with
      | (ses1,env1) -> ((FStar_List.rev_append ses1 []), env1)
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      fun push_before_typechecking  ->
        let verify =
          FStar_Options.should_verify
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let action = if verify then "Verifying" else "Lax-checking"  in
        let label1 =
          if modul.FStar_Syntax_Syntax.is_interface
          then "interface"
          else "implementation"  in
        (let uu____8000 = FStar_Options.debug_any ()  in
         if uu____8000
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
         let msg = Prims.strcat "Internals for " name  in
         let env1 =
           let uu___88_8006 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___88_8006.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___88_8006.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___88_8006.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___88_8006.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___88_8006.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___88_8006.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___88_8006.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___88_8006.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___88_8006.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___88_8006.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___88_8006.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___88_8006.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___88_8006.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___88_8006.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___88_8006.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___88_8006.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___88_8006.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___88_8006.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___88_8006.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___88_8006.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___88_8006.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___88_8006.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___88_8006.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___88_8006.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___88_8006.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___88_8006.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___88_8006.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___88_8006.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___88_8006.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___88_8006.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___88_8006.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___88_8006.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___88_8006.FStar_TypeChecker_Env.dep_graph)
           }  in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name
             in
          let uu____8010 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations  in
          match uu____8010 with
          | (ses,env3) ->
              ((let uu___89_8028 = modul  in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___89_8028.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.is_interface =
                    (uu___89_8028.FStar_Syntax_Syntax.is_interface)
                }), env3)))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____8046 = tc_decls env decls  in
        match uu____8046 with
        | (ses,env1) ->
            let modul1 =
              let uu___90_8064 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___90_8064.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.is_interface =
                  (uu___90_8064.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, env1)
  
let (finish_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      let env1 = FStar_TypeChecker_Env.finish_module env modul  in
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
        (Prims.strcat "Ending modul "
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
        env1 modul;
      (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
      (let uu____8080 =
         let uu____8081 = FStar_Options.interactive ()  in
         Prims.op_Negation uu____8081  in
       if uu____8080
       then
         let uu____8082 = FStar_Options.restore_cmd_line_options true  in
         FStar_All.pipe_right uu____8082 FStar_Pervasives.ignore
       else ());
      (modul, env1)
  
let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name
         in
      (let uu____8092 =
         let uu____8093 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
         Prims.strcat "Internals for " uu____8093  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____8092);
      (let env2 =
         FStar_List.fold_left
           (fun env2  ->
              fun se  ->
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
                let lids = FStar_Syntax_Util.lids_of_sigelt se  in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____8112 =
                          FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                        ()));
                env3) env1 modul.FStar_Syntax_Syntax.declarations
          in
       let uu____8133 = finish_partial_modul env2 modul  in
       FStar_Pervasives_Native.snd uu____8133)
  
let (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun modul  ->
      let uu____8148 = tc_partial_modul env modul true  in
      match uu____8148 with
      | (modul1,env1) -> finish_partial_modul env1 modul1
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible  in
      let filter_out_abstract =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               ((q = FStar_Syntax_Syntax.Abstract) ||
                  (q = FStar_Syntax_Syntax.Irreducible)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               ((((q = FStar_Syntax_Syntax.Abstract) ||
                    (q = FStar_Syntax_Syntax.Noeq))
                   || (q = FStar_Syntax_Syntax.Unopteq))
                  || (q = FStar_Syntax_Syntax.Irreducible)))
         in
      let add_assume_if_needed quals =
        if FStar_List.contains FStar_Syntax_Syntax.Assumption quals
        then quals
        else FStar_Syntax_Syntax.Assumption :: quals  in
      let is_unfold_or_inline =
        FStar_List.existsb
          (fun q  ->
             (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) ||
               (q = FStar_Syntax_Syntax.Inline_for_extraction))
         in
      let added_vals = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l ->
                 let uu____8240 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____8240
             | FStar_Syntax_Syntax.Projector (l,uu____8343) ->
                 let uu____8344 =
                   FStar_ST.op_Bang abstract_inductive_datacons  in
                 FStar_List.existsb (fun l'  -> FStar_Ident.lid_equals l l')
                   uu____8344
             | uu____8446 -> false) quals
         in
      let mk_typ_for_abstract_inductive bs t r =
        match bs with
        | [] -> t
        | uu____8461 ->
            (match t.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow
                      ((FStar_List.append bs bs'), c))
                   FStar_Pervasives_Native.None r
             | uu____8492 ->
                 let uu____8493 =
                   let uu____8496 =
                     let uu____8497 =
                       let uu____8510 = FStar_Syntax_Syntax.mk_Total t  in
                       (bs, uu____8510)  in
                     FStar_Syntax_Syntax.Tm_arrow uu____8497  in
                   FStar_Syntax_Syntax.mk uu____8496  in
                 uu____8493 FStar_Pervasives_Native.None r)
         in
      let val_has_already_been_added lids =
        FStar_List.existsML
          (fun lid  ->
             let uu____8525 = FStar_ST.op_Bang added_vals  in
             FStar_List.existsML
               (fun lid'  -> FStar_Ident.lid_equals lid lid') uu____8525)
          lids
         in
      let extract_lbs_annotations lbs r =
        FStar_List.fold_left
          (fun uu____8666  ->
             fun lb  ->
               match uu____8666 with
               | (l,b) ->
                   (match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                    with
                    | FStar_Syntax_Syntax.Tm_unknown  ->
                        (match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
                         with
                         | FStar_Syntax_Syntax.Tm_ascribed
                             (uu____8710,(FStar_Util.Inr c,uu____8712),uu____8713)
                             -> (((FStar_Syntax_Util.comp_result c) :: l), b)
                         | FStar_Syntax_Syntax.Tm_ascribed
                             (uu____8766,(FStar_Util.Inl t,uu____8768),uu____8769)
                             -> ((t :: l), b)
                         | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____8824) ->
                             (match e.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____8853,(FStar_Util.Inr c,uu____8855),uu____8856)
                                  ->
                                  let uu____8903 =
                                    let uu____8908 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                        FStar_Pervasives_Native.None r
                                       in
                                    uu____8908 :: l  in
                                  (uu____8903, b)
                              | FStar_Syntax_Syntax.Tm_ascribed
                                  (uu____8925,(FStar_Util.Inl t,uu____8927),uu____8928)
                                  ->
                                  let c =
                                    let uu____8976 = FStar_Options.ml_ish ()
                                       in
                                    if uu____8976
                                    then FStar_Syntax_Util.ml_comp t r
                                    else FStar_Syntax_Syntax.mk_Total t  in
                                  let uu____8978 =
                                    let uu____8983 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                                        FStar_Pervasives_Native.None r
                                       in
                                    uu____8983 :: l  in
                                  (uu____8978, b)
                              | uu____8998 ->
                                  (((lb.FStar_Syntax_Syntax.lbtyp) :: l),
                                    true))
                         | uu____9005 ->
                             (((lb.FStar_Syntax_Syntax.lbtyp) :: l), true))
                    | uu____9012 ->
                        (((lb.FStar_Syntax_Syntax.lbtyp) :: l), b)))
          ([], false) lbs
         in
      let is_pure_or_ghost_function_with_non_unit_type typs =
        FStar_List.existsML
          (fun t  ->
             (FStar_Syntax_Util.is_pure_or_ghost_function t) &&
               (let uu____9036 = FStar_Syntax_Util.is_unit t  in
                Prims.op_Negation uu____9036)) typs
         in
      let is_unit1 typs =
        FStar_List.for_all (fun t  -> FStar_Syntax_Util.is_unit t) typs  in
      let vals_of_lbs s lbs lids typs quals =
        FStar_List.map3
          (fun lb  ->
             fun lid  ->
               fun typ  ->
                 let uu___91_9091 = s  in
                 let uu____9092 =
                   let uu____9095 = filter_out_abstract quals  in
                   FStar_Syntax_Syntax.Assumption :: uu____9095  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (lid, (lb.FStar_Syntax_Syntax.lbunivs), typ));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___91_9091.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____9092;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___91_9091.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___91_9091.FStar_Syntax_Syntax.sigattrs)
                 }) lbs lids typs
         in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____9108 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____9127 ->
            failwith "Impossible! Bare data constructor"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_List.fold_left
                (fun sigelts1  ->
                   fun s1  ->
                     match s1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uvs,bs,t,uu____9178,uu____9179) ->
                         let s' =
                           let uu____9189 =
                             let uu____9196 =
                               mk_typ_for_abstract_inductive bs t
                                 s1.FStar_Syntax_Syntax.sigrng
                                in
                             (lid, uvs, uu____9196)  in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____9189  in
                         let uu____9197 =
                           let uu___92_9198 = s1  in
                           let uu____9199 =
                             let uu____9202 =
                               filter_out_abstract_and_noeq
                                 s1.FStar_Syntax_Syntax.sigquals
                                in
                             FStar_Syntax_Syntax.Assumption :: uu____9202  in
                           {
                             FStar_Syntax_Syntax.sigel = s';
                             FStar_Syntax_Syntax.sigrng =
                               (uu___92_9198.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = uu____9199;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___92_9198.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___92_9198.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         uu____9197 :: sigelts1
                     | FStar_Syntax_Syntax.Sig_datacon
                         (lid,uu____9206,uu____9207,uu____9208,uu____9209,uu____9210)
                         ->
                         ((let uu____9216 =
                             let uu____9219 =
                               FStar_ST.op_Bang abstract_inductive_datacons
                                in
                             lid :: uu____9219  in
                           FStar_ST.op_Colon_Equals
                             abstract_inductive_datacons uu____9216);
                          sigelts1)
                     | uu____9416 ->
                         failwith
                           "Impossible! Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                [] sigelts
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
            let uu____9423 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals
               in
            if uu____9423
            then []
            else
              if is_unfold_or_inline s.FStar_Syntax_Syntax.sigquals
              then []
              else
                ((let uu____9431 =
                    let uu____9434 = FStar_ST.op_Bang added_vals  in lid ::
                      uu____9434
                     in
                  FStar_ST.op_Colon_Equals added_vals uu____9431);
                 (let uu____9631 =
                    let uu___93_9632 = s  in
                    let uu____9633 =
                      let uu____9636 =
                        filter_out_abstract s.FStar_Syntax_Syntax.sigquals
                         in
                      add_assume_if_needed uu____9636  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___93_9632.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___93_9632.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____9633;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___93_9632.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___93_9632.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____9631]))
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____9645 = val_has_already_been_added lids  in
            if uu____9645
            then []
            else
              (let uu____9649 =
                 is_projector_or_discriminator_of_an_abstract_inductive
                   s.FStar_Syntax_Syntax.sigquals
                  in
               if uu____9649
               then []
               else
                 (let uu____9653 =
                    extract_lbs_annotations (FStar_Pervasives_Native.snd lbs)
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  match uu____9653 with
                  | (typs,b) ->
                      if
                        (is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                          (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)
                      then
                        (if b
                         then
                           let uu____9674 =
                             let uu____9675 =
                               let uu____9676 =
                                 let uu____9677 = FStar_List.hd lids  in
                                 uu____9677.FStar_Ident.str  in
                               Prims.strcat uu____9676 "\n\n"  in
                             Prims.strcat
                               "Abstract and irreducible defns must be annotated at the top-level: "
                               uu____9675
                              in
                           failwith uu____9674
                         else
                           vals_of_lbs s (FStar_Pervasives_Native.snd lbs)
                             lids typs s.FStar_Syntax_Syntax.sigquals)
                      else
                        if b
                        then [s]
                        else
                          (let uu____9687 =
                             is_pure_or_ghost_function_with_non_unit_type
                               typs
                              in
                           if uu____9687
                           then [s]
                           else
                             (let uu____9691 =
                                let uu____9692 = is_unit1 typs  in
                                Prims.op_Negation uu____9692  in
                              if uu____9691
                              then [s]
                              else
                                vals_of_lbs s
                                  (FStar_Pervasives_Native.snd lbs) lids typs
                                  s.FStar_Syntax_Syntax.sigquals))))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith "Did not anticipate this would arise"
        | FStar_Syntax_Syntax.Sig_assume (lids,uvs,t) ->
            let uu____9704 =
              let uu___94_9705 = s  in
              let uu____9706 =
                filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___94_9705.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___94_9705.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____9706;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___94_9705.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___94_9705.FStar_Syntax_Syntax.sigattrs)
              }  in
            [uu____9704]
        | FStar_Syntax_Syntax.Sig_new_effect uu____9709 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9710 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____9711 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9712 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____9725 -> [s]  in
      let uu___95_9726 = m  in
      let uu____9727 =
        let uu____9728 =
          FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations
           in
        FStar_List.flatten uu____9728  in
      {
        FStar_Syntax_Syntax.name = (uu___95_9726.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9727;
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      (let uu____9746 = FStar_Options.debug_any ()  in
       if uu____9746
       then
         let uu____9747 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____9747
       else ());
      (let env1 =
         let uu___96_9751 = env  in
         let uu____9752 =
           let uu____9753 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____9753  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___96_9751.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___96_9751.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___96_9751.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___96_9751.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___96_9751.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___96_9751.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___96_9751.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___96_9751.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___96_9751.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___96_9751.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___96_9751.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___96_9751.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___96_9751.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___96_9751.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___96_9751.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___96_9751.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___96_9751.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___96_9751.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____9752;
           FStar_TypeChecker_Env.lax_universes =
             (uu___96_9751.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___96_9751.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___96_9751.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___96_9751.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___96_9751.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___96_9751.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___96_9751.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___96_9751.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___96_9751.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___96_9751.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___96_9751.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___96_9751.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___96_9751.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___96_9751.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___96_9751.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___96_9751.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____9754 = tc_modul env1 m  in
       match uu____9754 with
       | (m1,env2) ->
           ((let uu____9766 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____9766
             then
               let uu____9767 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "%s\n" uu____9767
             else ());
            (let uu____9770 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____9770
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
                       let uu____9801 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____9801 with
                       | (univnames1,e) ->
                           let uu___97_9808 = lb  in
                           let uu____9809 =
                             let uu____9812 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____9812 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___97_9808.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___97_9808.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___97_9808.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___97_9808.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9809
                           }
                        in
                     let uu___98_9813 = se  in
                     let uu____9814 =
                       let uu____9815 =
                         let uu____9822 =
                           let uu____9829 = FStar_List.map update lbs  in
                           (b, uu____9829)  in
                         (uu____9822, ids)  in
                       FStar_Syntax_Syntax.Sig_let uu____9815  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9814;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___98_9813.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___98_9813.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___98_9813.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___98_9813.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9842 -> se  in
               let normalized_module =
                 let uu___99_9844 = m1  in
                 let uu____9845 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___99_9844.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9845;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___99_9844.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____9846 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____9846
             else ());
            (m1, env2)))
  