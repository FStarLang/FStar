open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____12 l in
          let uu___357_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___357_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___357_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___357_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___357_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___357_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___357_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___357_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___357_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___357_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___357_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___357_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___357_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___357_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___357_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___357_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___357_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___357_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___357_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___357_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___357_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___357_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___357_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___357_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___357_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___357_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___357_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___357_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___357_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___357_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___357_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___357_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___357_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___357_13.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l in
          let uu___358_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___358_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___358_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___358_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___358_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___358_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___358_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___358_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___358_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___358_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___358_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___358_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___358_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___358_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___358_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___358_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___358_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___358_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___358_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___358_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___358_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___358_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___358_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___358_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___358_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___358_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___358_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___358_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___358_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___358_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___358_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___358_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___358_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___358_29.FStar_TypeChecker_Env.dep_graph)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____38 =
         let uu____39 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39 in
       Prims.op_Negation uu____38)
let get_tactic_fv:
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
              let uu____66 = FStar_Syntax_Subst.compress h' in
              uu____66.FStar_Syntax_Syntax.n in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____72 -> FStar_Pervasives_Native.None)
        | uu____73 -> FStar_Pervasives_Native.None
let is_builtin_tactic: FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____80 =
        let uu____83 = FStar_List.splitAt (Prims.parse_int "2") path in
        FStar_Pervasives_Native.fst uu____83 in
      match uu____80 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____96 -> false
    else false
let user_tactics_modules: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____133 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____133 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____154 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____154
         then
           let uu____155 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____155
         else ());
        (let uu____157 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____157 with
         | (t',uu____165,uu____166) ->
             ((let uu____168 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____168
               then
                 let uu____169 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____169
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____180 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____180
let check_nogen:
  'Auu____185 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____185 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____205 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____205)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____232 =
          let uu____233 =
            let uu____234 =
              let uu____239 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____239, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____234 in
          FStar_Exn.raise uu____233 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____279)::(wp,uu____281)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____296 -> fail ())
        | uu____297 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____304 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____304 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____330 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____330 t in
          let open_univs_binders n_binders bs =
            let uu____340 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____340 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____348 =
            let uu____355 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders in
            let uu____356 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____355 uu____356 in
          (match uu____348 with
           | (effect_params_un,signature_un,opening) ->
               let uu____366 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
               (match uu____366 with
                | (effect_params,env,uu____375) ->
                    let uu____376 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un in
                    (match uu____376 with
                     | (signature,uu____382) ->
                         let ed1 =
                           let uu___359_384 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___359_384.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___359_384.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___359_384.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___359_384.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___359_384.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___359_384.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___359_384.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___359_384.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___359_384.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___359_384.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___359_384.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___359_384.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___359_384.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___359_384.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___359_384.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___359_384.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___359_384.FStar_Syntax_Syntax.actions)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____400 ->
                               let op uu____422 =
                                 match uu____422 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____442 =
                                       let uu____443 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____452 =
                                         open_univs (n_effect_params + n_us)
                                           t in
                                       FStar_Syntax_Subst.subst uu____443
                                         uu____452 in
                                     (us, uu____442) in
                               let uu___360_465 = ed1 in
                               let uu____466 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____467 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____468 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____469 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____470 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____471 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____472 =
                                 op ed1.FStar_Syntax_Syntax.assert_p in
                               let uu____473 =
                                 op ed1.FStar_Syntax_Syntax.assume_p in
                               let uu____474 =
                                 op ed1.FStar_Syntax_Syntax.null_wp in
                               let uu____475 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____476 =
                                 let uu____477 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____477 in
                               let uu____488 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____489 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____490 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___361_498 = a in
                                      let uu____499 =
                                        let uu____500 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____500 in
                                      let uu____511 =
                                        let uu____512 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd uu____512 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___361_498.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___361_498.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___361_498.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___361_498.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____499;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____511
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___360_465.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___360_465.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___360_465.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___360_465.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____466;
                                 FStar_Syntax_Syntax.bind_wp = uu____467;
                                 FStar_Syntax_Syntax.if_then_else = uu____468;
                                 FStar_Syntax_Syntax.ite_wp = uu____469;
                                 FStar_Syntax_Syntax.stronger = uu____470;
                                 FStar_Syntax_Syntax.close_wp = uu____471;
                                 FStar_Syntax_Syntax.assert_p = uu____472;
                                 FStar_Syntax_Syntax.assume_p = uu____473;
                                 FStar_Syntax_Syntax.null_wp = uu____474;
                                 FStar_Syntax_Syntax.trivial = uu____475;
                                 FStar_Syntax_Syntax.repr = uu____476;
                                 FStar_Syntax_Syntax.return_repr = uu____488;
                                 FStar_Syntax_Syntax.bind_repr = uu____489;
                                 FStar_Syntax_Syntax.actions = uu____490
                               } in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____549 =
                               let uu____550 =
                                 let uu____555 =
                                   FStar_TypeChecker_Err.unexpected_signature_for_monad
                                     env1 mname t in
                                 (uu____555,
                                   (FStar_Ident.range_of_lid mname)) in
                               FStar_Errors.Error uu____550 in
                             FStar_Exn.raise uu____549 in
                           let uu____562 =
                             let uu____563 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____563.FStar_Syntax_Syntax.n in
                           match uu____562 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a,uu____598)::(wp,uu____600)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____615 -> fail signature1)
                           | uu____616 -> fail signature1 in
                         let uu____617 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____617 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____639 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____646 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un in
                                    (match uu____646 with
                                     | (signature1,uu____658) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____659 ->
                                    let uu____662 =
                                      let uu____667 =
                                        let uu____668 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____668) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____667 in
                                    (match uu____662 with
                                     | (uu____677,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env1 =
                                let uu____680 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env uu____680 in
                              ((let uu____682 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____682
                                then
                                  let uu____683 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____684 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____685 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____686 =
                                    let uu____687 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____687 in
                                  let uu____688 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____683 uu____684 uu____685 uu____686
                                    uu____688
                                else ());
                               (let check_and_gen' env2 uu____704 k =
                                  match uu____704 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____718::uu____719 ->
                                           let uu____722 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____722 with
                                            | (us1,t1) ->
                                                let uu____731 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____731 with
                                                 | (us2,t2) ->
                                                     let uu____738 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k in
                                                     let uu____739 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____739)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____744 =
                                      let uu____751 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____752 =
                                        let uu____755 =
                                          let uu____756 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____756 in
                                        [uu____755] in
                                      uu____751 :: uu____752 in
                                    let uu____757 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____744
                                      uu____757 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____761 = fresh_effect_signature () in
                                  match uu____761 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____777 =
                                          let uu____784 =
                                            let uu____785 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____785 in
                                          [uu____784] in
                                        let uu____786 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____777
                                          uu____786 in
                                      let expected_k =
                                        let uu____792 =
                                          let uu____799 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____800 =
                                            let uu____803 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____804 =
                                              let uu____807 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____808 =
                                                let uu____811 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____812 =
                                                  let uu____815 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____815] in
                                                uu____811 :: uu____812 in
                                              uu____807 :: uu____808 in
                                            uu____803 :: uu____804 in
                                          uu____799 :: uu____800 in
                                        let uu____816 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____792
                                          uu____816 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____821 =
                                      let uu____822 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____822
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____821 in
                                  let expected_k =
                                    let uu____834 =
                                      let uu____841 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____842 =
                                        let uu____845 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____846 =
                                          let uu____849 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____850 =
                                            let uu____853 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____853] in
                                          uu____849 :: uu____850 in
                                        uu____845 :: uu____846 in
                                      uu____841 :: uu____842 in
                                    let uu____854 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____834
                                      uu____854 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____861 =
                                      let uu____868 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____869 =
                                        let uu____872 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____872] in
                                      uu____868 :: uu____869 in
                                    let uu____873 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____861
                                      uu____873 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____877 = FStar_Syntax_Util.type_u () in
                                  match uu____877 with
                                  | (t,uu____883) ->
                                      let expected_k =
                                        let uu____887 =
                                          let uu____894 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____895 =
                                            let uu____898 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____899 =
                                              let uu____902 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____902] in
                                            uu____898 :: uu____899 in
                                          uu____894 :: uu____895 in
                                        let uu____903 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____887
                                          uu____903 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____908 =
                                      let uu____909 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____909
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____908 in
                                  let b_wp_a =
                                    let uu____921 =
                                      let uu____928 =
                                        let uu____929 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____929 in
                                      [uu____928] in
                                    let uu____930 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____921
                                      uu____930 in
                                  let expected_k =
                                    let uu____936 =
                                      let uu____943 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____944 =
                                        let uu____947 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____948 =
                                          let uu____951 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____951] in
                                        uu____947 :: uu____948 in
                                      uu____943 :: uu____944 in
                                    let uu____952 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____936
                                      uu____952 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let assert_p =
                                  let expected_k =
                                    let uu____959 =
                                      let uu____966 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____967 =
                                        let uu____970 =
                                          let uu____971 =
                                            let uu____972 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____972
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____971 in
                                        let uu____981 =
                                          let uu____984 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____984] in
                                        uu____970 :: uu____981 in
                                      uu____966 :: uu____967 in
                                    let uu____985 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____959
                                      uu____985 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k in
                                let assume_p =
                                  let expected_k =
                                    let uu____992 =
                                      let uu____999 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1000 =
                                        let uu____1003 =
                                          let uu____1004 =
                                            let uu____1005 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____1005
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1004 in
                                        let uu____1014 =
                                          let uu____1017 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1017] in
                                        uu____1003 :: uu____1014 in
                                      uu____999 :: uu____1000 in
                                    let uu____1018 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____992
                                      uu____1018 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k in
                                let null_wp =
                                  let expected_k =
                                    let uu____1025 =
                                      let uu____1032 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      [uu____1032] in
                                    let uu____1033 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1025
                                      uu____1033 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1037 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1037 with
                                  | (t,uu____1043) ->
                                      let expected_k =
                                        let uu____1047 =
                                          let uu____1054 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1055 =
                                            let uu____1058 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1058] in
                                          uu____1054 :: uu____1055 in
                                        let uu____1059 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1047
                                          uu____1059 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1062 =
                                  let uu____1073 =
                                    let uu____1074 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1074.FStar_Syntax_Syntax.n in
                                  match uu____1073 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1089 ->
                                      let repr =
                                        let uu____1091 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1091 with
                                        | (t,uu____1097) ->
                                            let expected_k =
                                              let uu____1101 =
                                                let uu____1108 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1109 =
                                                  let uu____1112 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1112] in
                                                uu____1108 :: uu____1109 in
                                              let uu____1113 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1101 uu____1113 in
                                            tc_check_trivial_guard env1
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env1 repr in
                                        let uu____1126 =
                                          let uu____1129 =
                                            let uu____1130 =
                                              let uu____1145 =
                                                let uu____1148 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1149 =
                                                  let uu____1152 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1152] in
                                                uu____1148 :: uu____1149 in
                                              (repr1, uu____1145) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1130 in
                                          FStar_Syntax_Syntax.mk uu____1129 in
                                        uu____1126
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1167 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1167 wp in
                                      let destruct_repr t =
                                        let uu____1180 =
                                          let uu____1181 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1181.FStar_Syntax_Syntax.n in
                                        match uu____1180 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1192,(t1,uu____1194)::
                                             (wp,uu____1196)::[])
                                            -> (t1, wp)
                                        | uu____1239 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____1250 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____1250
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____1251 =
                                          fresh_effect_signature () in
                                        match uu____1251 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1267 =
                                                let uu____1274 =
                                                  let uu____1275 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1275 in
                                                [uu____1274] in
                                              let uu____1276 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____1267 uu____1276 in
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
                                              let uu____1282 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1282 in
                                            let wp_g_x =
                                              let uu____1286 =
                                                let uu____1287 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____1288 =
                                                  let uu____1289 =
                                                    let uu____1290 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1290 in
                                                  [uu____1289] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1287 uu____1288 in
                                              uu____1286
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____1299 =
                                                  let uu____1300 =
                                                    let uu____1301 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____1301
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____1310 =
                                                    let uu____1311 =
                                                      let uu____1314 =
                                                        let uu____1317 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____1318 =
                                                          let uu____1321 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____1322 =
                                                            let uu____1325 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____1326 =
                                                              let uu____1329
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____1329] in
                                                            uu____1325 ::
                                                              uu____1326 in
                                                          uu____1321 ::
                                                            uu____1322 in
                                                        uu____1317 ::
                                                          uu____1318 in
                                                      r :: uu____1314 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1311 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1300 uu____1310 in
                                                uu____1299
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let expected_k =
                                              let uu____1335 =
                                                let uu____1342 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1343 =
                                                  let uu____1346 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____1347 =
                                                    let uu____1350 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____1351 =
                                                      let uu____1354 =
                                                        let uu____1355 =
                                                          let uu____1356 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____1356 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1355 in
                                                      let uu____1357 =
                                                        let uu____1360 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____1361 =
                                                          let uu____1364 =
                                                            let uu____1365 =
                                                              let uu____1366
                                                                =
                                                                let uu____1373
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____1373] in
                                                              let uu____1374
                                                                =
                                                                let uu____1377
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1377 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1366
                                                                uu____1374 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1365 in
                                                          [uu____1364] in
                                                        uu____1360 ::
                                                          uu____1361 in
                                                      uu____1354 ::
                                                        uu____1357 in
                                                    uu____1350 :: uu____1351 in
                                                  uu____1346 :: uu____1347 in
                                                uu____1342 :: uu____1343 in
                                              let uu____1378 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____1335 uu____1378 in
                                            let uu____1381 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k in
                                            (match uu____1381 with
                                             | (expected_k1,uu____1389,uu____1390)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env3 =
                                                   let uu___362_1395 = env2 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___362_1395.FStar_TypeChecker_Env.dep_graph)
                                                   } in
                                                 let br =
                                                   check_and_gen' env3
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____1405 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1405 in
                                        let res =
                                          let wp =
                                            let uu____1412 =
                                              let uu____1413 =
                                                let uu____1414 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____1414
                                                  FStar_Pervasives_Native.snd in
                                              let uu____1423 =
                                                let uu____1424 =
                                                  let uu____1427 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____1428 =
                                                    let uu____1431 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____1431] in
                                                  uu____1427 :: uu____1428 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1424 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1413 uu____1423 in
                                            uu____1412
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____1437 =
                                            let uu____1444 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1445 =
                                              let uu____1448 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____1448] in
                                            uu____1444 :: uu____1445 in
                                          let uu____1449 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____1437
                                            uu____1449 in
                                        let uu____1452 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k in
                                        match uu____1452 with
                                        | (expected_k1,uu____1466,uu____1467)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____1471 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____1471 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1492 ->
                                                      FStar_Exn.raise
                                                        (FStar_Errors.Error
                                                           ("Unexpected universe-polymorphic return for effect",
                                                             (repr1.FStar_Syntax_Syntax.pos))))) in
                                      let actions =
                                        let check_action act =
                                          let uu____1517 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ in
                                          match uu____1517 with
                                          | (act_typ,uu____1525,g_t) ->
                                              let env' =
                                                let uu___363_1528 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___363_1528.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___363_1528.FStar_TypeChecker_Env.dep_graph)
                                                } in
                                              ((let uu____1530 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED") in
                                                if uu____1530
                                                then
                                                  let uu____1531 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn in
                                                  let uu____1532 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1531 uu____1532
                                                else ());
                                               (let uu____1534 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn in
                                                match uu____1534 with
                                                | (act_defn,uu____1542,g_a)
                                                    ->
                                                    let act_defn1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant]
                                                        env1 act_defn in
                                                    let act_typ1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant;
                                                        FStar_TypeChecker_Normalize.Eager_unfolding;
                                                        FStar_TypeChecker_Normalize.Beta]
                                                        env1 act_typ in
                                                    let uu____1546 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1 in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1574 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c in
                                                          (match uu____1574
                                                           with
                                                           | (bs1,uu____1584)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun in
                                                               let k =
                                                                 let uu____1591
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1591 in
                                                               let uu____1594
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k in
                                                               (match uu____1594
                                                                with
                                                                | (k1,uu____1606,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1608 ->
                                                          let uu____1609 =
                                                            let uu____1610 =
                                                              let uu____1615
                                                                =
                                                                let uu____1616
                                                                  =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    act_typ2 in
                                                                let uu____1617
                                                                  =
                                                                  FStar_Syntax_Print.tag_of_term
                                                                    act_typ2 in
                                                                FStar_Util.format2
                                                                  "Actions must have function types (not: %s, a.k.a. %s)"
                                                                  uu____1616
                                                                  uu____1617 in
                                                              (uu____1615,
                                                                (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                            FStar_Errors.Error
                                                              uu____1610 in
                                                          FStar_Exn.raise
                                                            uu____1609 in
                                                    (match uu____1546 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k in
                                                         ((let uu____1626 =
                                                             let uu____1627 =
                                                               let uu____1628
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1628 in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1627 in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1626);
                                                          (let act_typ2 =
                                                             let uu____1632 =
                                                               let uu____1633
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k in
                                                               uu____1633.FStar_Syntax_Syntax.n in
                                                             match uu____1632
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1656
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                 (match uu____1656
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1665
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____1665
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1687
                                                                    =
                                                                    let uu____1688
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1688] in
                                                                    let uu____1689
                                                                    =
                                                                    let uu____1698
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1698] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1687;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1689;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1699
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1699))
                                                             | uu____1702 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)" in
                                                           let uu____1705 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1 in
                                                           match uu____1705
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ3 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ2 in
                                                               let act_typ4 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ3 in
                                                               let uu___364_1714
                                                                 = act in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___364_1714.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___364_1714.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___364_1714.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ4
                                                               }))))) in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action) in
                                      (repr, bind_repr, return_repr, actions) in
                                match uu____1062 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1738 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1738 in
                                    let uu____1741 =
                                      let uu____1748 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____1748 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1769 ->
                                               let uu____1772 =
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
                                                             (Prims.parse_int
                                                                "0"))
                                                      gen_univs
                                                      annotated_univ_names) in
                                               if uu____1772
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1786 =
                                                    let uu____1787 =
                                                      let uu____1792 =
                                                        let uu____1793 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               annotated_univ_names) in
                                                        let uu____1794 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               gen_univs) in
                                                        FStar_Util.format2
                                                          "Expected an effect definition with %s universes; but found %s"
                                                          uu____1793
                                                          uu____1794 in
                                                      (uu____1792,
                                                        ((ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                                    FStar_Errors.Error
                                                      uu____1787 in
                                                  FStar_Exn.raise uu____1786)) in
                                    (match uu____1741 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1808 =
                                             let uu____1813 =
                                               let uu____1814 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____1814.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____1813) in
                                           match uu____1808 with
                                           | ([],uu____1817) -> t
                                           | (uu____1828,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1829,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1847 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1860 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1860 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____1865 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1867 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____1867))
                                                && (m <> n1) in
                                            if uu____1865
                                            then
                                              let error1 =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____1883 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____1884 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format3
                                                  "The effect combinator is %s (n=%s) (%s)"
                                                  error1 uu____1883
                                                  uu____1884 in
                                              FStar_Exn.raise
                                                (FStar_Errors.Error
                                                   (err_msg,
                                                     ((FStar_Pervasives_Native.snd
                                                         ts1).FStar_Syntax_Syntax.pos)))
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____1892 =
                                             close1 (- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____1892 with
                                           | (univs2,defn) ->
                                               let uu____1899 =
                                                 close1
                                                   (- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____1899 with
                                                | (univs',typ) ->
                                                    let uu___365_1909 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___365_1909.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___365_1909.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___365_1909.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___366_1914 = ed2 in
                                           let uu____1915 =
                                             close1 (Prims.parse_int "0")
                                               return_wp in
                                           let uu____1916 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp in
                                           let uu____1917 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1 in
                                           let uu____1918 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp in
                                           let uu____1919 =
                                             close1 (Prims.parse_int "0")
                                               stronger in
                                           let uu____1920 =
                                             close1 (Prims.parse_int "1")
                                               close_wp in
                                           let uu____1921 =
                                             close1 (Prims.parse_int "0")
                                               assert_p in
                                           let uu____1922 =
                                             close1 (Prims.parse_int "0")
                                               assume_p in
                                           let uu____1923 =
                                             close1 (Prims.parse_int "0")
                                               null_wp in
                                           let uu____1924 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp in
                                           let uu____1925 =
                                             let uu____1926 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____1926 in
                                           let uu____1937 =
                                             close1 (Prims.parse_int "0")
                                               return_repr in
                                           let uu____1938 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr in
                                           let uu____1939 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___366_1914.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___366_1914.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1915;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1916;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1917;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1918;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1919;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1920;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1921;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1922;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1923;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1924;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1925;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1937;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1938;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1939
                                           } in
                                         ((let uu____1943 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____1943
                                           then
                                             let uu____1944 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____1944
                                           else ());
                                          ed3))))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____1962 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1962 with
      | (effect_binders_un,signature_un) ->
          let uu____1979 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1979 with
           | (effect_binders,env1,uu____1998) ->
               let uu____1999 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1999 with
                | (signature,uu____2015) ->
                    let raise_error err_msg =
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           (err_msg, (signature.FStar_Syntax_Syntax.pos))) in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2043  ->
                           match uu____2043 with
                           | (bv,qual) ->
                               let uu____2054 =
                                 let uu___367_2055 = bv in
                                 let uu____2056 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___367_2055.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___367_2055.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2056
                                 } in
                               (uu____2054, qual)) effect_binders in
                    let uu____2059 =
                      let uu____2066 =
                        let uu____2067 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2067.FStar_Syntax_Syntax.n in
                      match uu____2066 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____2077)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____2099 ->
                          raise_error
                            "bad shape for effect-for-free signature" in
                    (match uu____2059 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2123 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2123
                           then
                             let uu____2124 =
                               let uu____2127 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2127 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2124
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2161 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2161 with
                           | (t2,comp,uu____2174) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2181 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2181 with
                          | (repr,_comp) ->
                              ((let uu____2203 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2203
                                then
                                  let uu____2204 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2204
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____2210 =
                                    let uu____2211 =
                                      let uu____2212 =
                                        let uu____2227 =
                                          let uu____2234 =
                                            let uu____2239 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2240 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2239, uu____2240) in
                                          [uu____2234] in
                                        (wp_type1, uu____2227) in
                                      FStar_Syntax_Syntax.Tm_app uu____2212 in
                                    mk1 uu____2211 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2210 in
                                let effect_signature =
                                  let binders =
                                    let uu____2265 =
                                      let uu____2270 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2270) in
                                    let uu____2271 =
                                      let uu____2278 =
                                        let uu____2279 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2279
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2278] in
                                    uu____2265 :: uu____2271 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let effect_signature1 =
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
                                  let uu____2342 = item in
                                  match uu____2342 with
                                  | (u_item,item1) ->
                                      let uu____2363 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2363 with
                                       | (item2,item_comp) ->
                                           ((let uu____2379 =
                                               let uu____2380 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2380 in
                                             if uu____2379
                                             then
                                               let uu____2381 =
                                                 let uu____2382 =
                                                   let uu____2383 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2384 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2383 uu____2384 in
                                                 FStar_Errors.Err uu____2382 in
                                               FStar_Exn.raise uu____2381
                                             else ());
                                            (let uu____2386 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2386 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2406 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2406 with
                                | (dmff_env1,uu____2430,bind_wp,bind_elab) ->
                                    let uu____2433 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2433 with
                                     | (dmff_env2,uu____2457,return_wp,return_elab)
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
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____2464 =
                                             let uu____2465 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2465.FStar_Syntax_Syntax.n in
                                           match uu____2464 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2509 =
                                                 let uu____2524 =
                                                   let uu____2529 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2529 in
                                                 match uu____2524 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2593 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2509 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2632 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2632 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2649 =
                                                          let uu____2650 =
                                                            let uu____2665 =
                                                              let uu____2672
                                                                =
                                                                let uu____2677
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2678
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2677,
                                                                  uu____2678) in
                                                              [uu____2672] in
                                                            (wp_type1,
                                                              uu____2665) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2650 in
                                                        mk1 uu____2649 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2693 =
                                                      let uu____2702 =
                                                        let uu____2703 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2703 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2702 in
                                                    (match uu____2693 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2722
                                                           =
                                                           let error_msg =
                                                             let uu____2724 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2724
                                                               (match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           raise_error
                                                             error_msg in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               (if
                                                                  Prims.op_Negation
                                                                    (
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                then fail ()
                                                                else ();
                                                                (let uu____2730
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
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____2730
                                                                   FStar_Pervasives.ignore)));
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
                                                             let uu____2757 =
                                                               let uu____2758
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2759
                                                                 =
                                                                 let uu____2760
                                                                   =
                                                                   let uu____2767
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2767,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2760] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2758
                                                                 uu____2759 in
                                                             uu____2757
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2792 =
                                                             let uu____2793 =
                                                               let uu____2800
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2800] in
                                                             b11 ::
                                                               uu____2793 in
                                                           let uu____2805 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2792
                                                             uu____2805
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2806 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2808 =
                                             let uu____2809 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2809.FStar_Syntax_Syntax.n in
                                           match uu____2808 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2853 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2853
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2866 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2868 =
                                             let uu____2869 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2869.FStar_Syntax_Syntax.n in
                                           match uu____2868 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2896 =
                                                 let uu____2897 =
                                                   let uu____2900 =
                                                     let uu____2901 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2901 in
                                                   [uu____2900] in
                                                 FStar_List.append uu____2897
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2896 body what
                                           | uu____2902 ->
                                               raise_error
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2920 =
                                                let uu____2921 =
                                                  let uu____2922 =
                                                    let uu____2937 =
                                                      let uu____2938 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2938 in
                                                    (t, uu____2937) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2922 in
                                                mk1 uu____2921 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2920) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2968 = f a2 in
                                               [uu____2968]
                                           | x::xs ->
                                               let uu____2973 =
                                                 apply_last1 f xs in
                                               x :: uu____2973 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____2993 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2993 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3023 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3023
                                                 then
                                                   let uu____3024 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3024
                                                 else ());
                                                (let uu____3026 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3026))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3035 =
                                                 let uu____3040 = mk_lid name in
                                                 let uu____3041 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3040 uu____3041 in
                                               (match uu____3035 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3045 =
                                                        let uu____3048 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____3048 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3045);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3183 =
                                             let uu____3186 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3187 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3186 :: uu____3187 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3183);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3323 =
                                               let uu____3326 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3327 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3326 :: uu____3327 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3323);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3460 =
                                                FStar_List.fold_left
                                                  (fun uu____3500  ->
                                                     fun action  ->
                                                       match uu____3500 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3521 =
                                                             let uu____3528 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3528
                                                               params_un in
                                                           (match uu____3521
                                                            with
                                                            | (action_params,env',uu____3537)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3557
                                                                     ->
                                                                    match uu____3557
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3568
                                                                    =
                                                                    let uu___368_3569
                                                                    = bv in
                                                                    let uu____3570
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___368_3569.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___368_3569.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3570
                                                                    } in
                                                                    (uu____3568,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3574
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3574
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
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
                                                                    uu____3604
                                                                    ->
                                                                    let uu____3605
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3605 in
                                                                    ((
                                                                    let uu____3609
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3609
                                                                    then
                                                                    let uu____3610
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3611
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3612
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3613
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3610
                                                                    uu____3611
                                                                    uu____3612
                                                                    uu____3613
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu___369_3621
                                                                    = action in
                                                                    let uu____3622
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3623
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___369_3621.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___369_3621.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___369_3621.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3622;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3623
                                                                    } in
                                                                    uu____3620
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3617))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3460 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____3656 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3657 =
                                                        let uu____3660 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3660] in
                                                      uu____3656 ::
                                                        uu____3657 in
                                                    let uu____3661 =
                                                      let uu____3662 =
                                                        let uu____3663 =
                                                          let uu____3664 =
                                                            let uu____3679 =
                                                              let uu____3686
                                                                =
                                                                let uu____3691
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3692
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3691,
                                                                  uu____3692) in
                                                              [uu____3686] in
                                                            (repr,
                                                              uu____3679) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3664 in
                                                        mk1 uu____3663 in
                                                      let uu____3707 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3662
                                                        uu____3707 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3661
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3710 =
                                                    let uu____3717 =
                                                      let uu____3718 =
                                                        let uu____3721 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3721 in
                                                      uu____3718.FStar_Syntax_Syntax.n in
                                                    match uu____3717 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3731)
                                                        ->
                                                        let uu____3760 =
                                                          let uu____3777 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3777
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3835 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3760
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3885 =
                                                               let uu____3886
                                                                 =
                                                                 let uu____3889
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3889 in
                                                               uu____3886.FStar_Syntax_Syntax.n in
                                                             (match uu____3885
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3914
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3914
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3927
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3952
                                                                     ->
                                                                    match uu____3952
                                                                    with
                                                                    | 
                                                                    (bv,uu____3958)
                                                                    ->
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3960
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3959
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3927
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
                                                                    let uu____4024
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4024 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg)
                                                                    | 
                                                                    uu____4029
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4037
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4037 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg) in
                                                                    let uu____4042
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____4045
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____4042,
                                                                    uu____4045)))
                                                              | uu____4052 ->
                                                                  let uu____4053
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4054 in
                                                                  raise_error
                                                                    uu____4053))
                                                    | uu____4061 ->
                                                        let uu____4062 =
                                                          let uu____4063 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____4063 in
                                                        raise_error
                                                          uu____4062 in
                                                  (match uu____3710 with
                                                   | (pre,post) ->
                                                       ((let uu____4087 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____4089 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____4091 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___370_4093
                                                             = ed in
                                                           let uu____4094 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____4095 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____4096 =
                                                             let uu____4097 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____4097) in
                                                           let uu____4104 =
                                                             let uu____4105 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4105) in
                                                           let uu____4112 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____4113 =
                                                             let uu____4114 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4114) in
                                                           let uu____4121 =
                                                             let uu____4122 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4122) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4094;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4095;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4096;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4104;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___370_4093.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4112;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4113;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4121;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____4129 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4129
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4147
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4147
                                                               then
                                                                 let uu____4148
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4148
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____4160
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    let uu____4172
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4172) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4163 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4160;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4187
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4187
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4189
                                                                 =
                                                                 let uu____4192
                                                                   =
                                                                   let uu____4195
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4195 in
                                                                 FStar_List.append
                                                                   uu____4192
                                                                   sigelts' in
                                                               (uu____4189,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4271 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4271 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4304 = FStar_List.hd ses in
            uu____4304.FStar_Syntax_Syntax.sigrng in
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
           | uu____4309 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Invalid (partial) redefinition of lex_t", err_range)));
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4314,uu____4315);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4317;
               FStar_Syntax_Syntax.sigattrs = uu____4318;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4322);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4324;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4325;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4329);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4331;
                 FStar_Syntax_Syntax.sigattrs = uu____4332;_}::[]
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
                 let uu____4397 =
                   let uu____4400 =
                     let uu____4401 =
                       let uu____4408 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4408, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4401 in
                   FStar_Syntax_Syntax.mk uu____4400 in
                 uu____4397 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
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
                 } in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let lex_cons_t =
                 let a =
                   let uu____4426 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4426 in
                 let hd1 =
                   let uu____4428 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4428 in
                 let tl1 =
                   let uu____4430 =
                     let uu____4431 =
                       let uu____4434 =
                         let uu____4435 =
                           let uu____4442 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4442, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4435 in
                       FStar_Syntax_Syntax.mk uu____4434 in
                     uu____4431 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4430 in
                 let res =
                   let uu____4451 =
                     let uu____4454 =
                       let uu____4455 =
                         let uu____4462 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4462,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4455 in
                     FStar_Syntax_Syntax.mk uu____4454 in
                   uu____4451 FStar_Pervasives_Native.None r2 in
                 let uu____4468 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4468 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
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
                 } in
               let uu____4507 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4507;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4512 ->
               let err_msg =
                 let uu____4516 =
                   let uu____4517 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4517 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4516 in
               FStar_Exn.raise (FStar_Errors.Error (err_msg, err_range)))
let tc_assume:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r in
            let uu____4542 = FStar_Syntax_Util.type_u () in
            match uu____4542 with
            | (k,uu____4548) ->
                let phi1 =
                  let uu____4550 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4550
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4552 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4552 with
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
let tc_inductive:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____4594 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4594 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4627 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4627 FStar_List.flatten in
              ((let uu____4641 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4641
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
                          let uu____4652 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4662,uu____4663,uu____4664,uu____4665,uu____4666)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4675 -> failwith "Impossible!" in
                          match uu____4652 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4686 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4690,uu____4691,uu____4692,uu____4693,uu____4694)
                        -> lid
                    | uu____4703 -> failwith "Impossible" in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let res =
                  let uu____4721 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4721
                  then ([sig_bndle], data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume in
                     let uu____4744 =
                       let uu____4747 =
                         let uu____4748 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4748;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4747 :: ses1 in
                     (uu____4744, data_ops_ses)) in
                (let uu____4758 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4792 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4817 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____4869 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4869 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4908 = FStar_Options.set_options t s in
             match uu____4908 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s1), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____4934 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4934 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4942 = cps_and_elaborate env1 ne in
           (match uu____4942 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___371_4979 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___371_4979.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___371_4979.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___371_4979.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___371_4979.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___372_4981 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___372_4981.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___372_4981.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___372_4981.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___372_4981.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___373_4989 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___373_4989.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___373_4989.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___373_4989.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___373_4989.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4997 =
             let uu____5004 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5004 in
           (match uu____4997 with
            | (a,wp_a_src) ->
                let uu____5019 =
                  let uu____5026 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5026 in
                (match uu____5019 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5042 =
                         let uu____5045 =
                           let uu____5046 =
                             let uu____5053 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____5053) in
                           FStar_Syntax_Syntax.NT uu____5046 in
                         [uu____5045] in
                       FStar_Syntax_Subst.subst uu____5042 wp_b_tgt in
                     let expected_k =
                       let uu____5057 =
                         let uu____5064 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____5065 =
                           let uu____5068 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____5068] in
                         uu____5064 :: uu____5065 in
                       let uu____5069 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____5057 uu____5069 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5090 =
                           let uu____5091 =
                             let uu____5096 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____5097 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____5096, uu____5097) in
                           FStar_Errors.Error uu____5091 in
                         FStar_Exn.raise uu____5090 in
                       let uu____5100 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____5100 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____5132 =
                             let uu____5133 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____5133 in
                           if uu____5132
                           then no_reify eff_name
                           else
                             (let uu____5139 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____5140 =
                                let uu____5143 =
                                  let uu____5144 =
                                    let uu____5159 =
                                      let uu____5162 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5163 =
                                        let uu____5166 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5166] in
                                      uu____5162 :: uu____5163 in
                                    (repr, uu____5159) in
                                  FStar_Syntax_Syntax.Tm_app uu____5144 in
                                FStar_Syntax_Syntax.mk uu____5143 in
                              uu____5140 FStar_Pervasives_Native.None
                                uu____5139) in
                     let uu____5172 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5200,lift_wp)) ->
                           let uu____5224 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5224)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5250 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5250
                             then
                               let uu____5251 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5251
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____5254 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5254 with
                             | (lift1,comp,uu____5269) ->
                                 let uu____5270 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5270 with
                                  | (uu____5283,lift_wp,lift_elab) ->
                                      let uu____5286 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5287 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5172 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___374_5328 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___374_5328.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___374_5328.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___374_5328.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___374_5328.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___374_5328.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___374_5328.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___374_5328.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___374_5328.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___374_5328.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___374_5328.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___374_5328.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___374_5328.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___374_5328.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___374_5328.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___374_5328.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___374_5328.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___374_5328.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___374_5328.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___374_5328.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___374_5328.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___374_5328.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___374_5328.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___374_5328.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___374_5328.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___374_5328.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___374_5328.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___374_5328.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___374_5328.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___374_5328.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___374_5328.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___374_5328.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___374_5328.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___374_5328.FStar_TypeChecker_Env.dep_graph)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5334,lift1)
                                ->
                                let uu____5346 =
                                  let uu____5353 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5353 in
                                (match uu____5346 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv
                                         FStar_Pervasives_Native.None
                                         wp_a_src1 in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1 in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2
                                           (FStar_Pervasives_Native.snd
                                              lift_wp) in
                                       let lift_wp_a =
                                         let uu____5377 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5378 =
                                           let uu____5381 =
                                             let uu____5382 =
                                               let uu____5397 =
                                                 let uu____5400 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5401 =
                                                   let uu____5404 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5404] in
                                                 uu____5400 :: uu____5401 in
                                               (lift_wp1, uu____5397) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5382 in
                                           FStar_Syntax_Syntax.mk uu____5381 in
                                         uu____5378
                                           FStar_Pervasives_Native.None
                                           uu____5377 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5413 =
                                         let uu____5420 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5421 =
                                           let uu____5424 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5425 =
                                             let uu____5428 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5428] in
                                           uu____5424 :: uu____5425 in
                                         uu____5420 :: uu____5421 in
                                       let uu____5429 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5413
                                         uu____5429 in
                                     let uu____5432 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5432 with
                                      | (expected_k2,uu____5442,uu____5443)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___375_5446 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___375_5446.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___375_5446.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___376_5448 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___376_5448.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___376_5448.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___376_5448.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___376_5448.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5467 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5467 with
            | (tps1,c1) ->
                let uu____5482 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5482 with
                 | (tps2,env3,us) ->
                     let uu____5500 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5500 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5521 =
                              let uu____5522 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5522 in
                            match uu____5521 with
                            | (uvs1,t) ->
                                let uu____5537 =
                                  let uu____5550 =
                                    let uu____5555 =
                                      let uu____5556 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5556.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5555) in
                                  match uu____5550 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5571,c4)) -> ([], c4)
                                  | (uu____5611,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5638 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5537 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5682 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5682 with
                                         | (uu____5687,t1) ->
                                             let uu____5689 =
                                               let uu____5690 =
                                                 let uu____5695 =
                                                   let uu____5696 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5697 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5698 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5696 uu____5697
                                                     uu____5698 in
                                                 (uu____5695, r) in
                                               FStar_Errors.Error uu____5690 in
                                             FStar_Exn.raise uu____5689)
                                      else ();
                                      (let se1 =
                                         let uu___377_5701 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___377_5701.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___377_5701.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___377_5701.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___377_5701.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5718,uu____5719,uu____5720) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___352_5724  ->
                   match uu___352_5724 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5725 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5730,uu____5731) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___352_5739  ->
                   match uu___352_5739 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5740 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5750 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5750
             then
               let uu____5751 =
                 let uu____5752 =
                   let uu____5757 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5757, r) in
                 FStar_Errors.Error uu____5752 in
               FStar_Exn.raise uu____5751
             else ());
            (let uu____5759 =
               if uvs = []
               then
                 let uu____5760 =
                   let uu____5761 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5761 in
                 check_and_gen env2 t uu____5760
               else
                 (let uu____5767 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5767 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5775 =
                          let uu____5776 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5776 in
                        tc_check_trivial_guard env2 t1 uu____5775 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5782 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5782)) in
             match uu____5759 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___378_5798 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___378_5798.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___378_5798.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___378_5798.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___378_5798.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5808 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5808 with
            | (uu____5821,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5831 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5831 with
            | (e1,c,g1) ->
                let uu____5849 =
                  let uu____5856 =
                    let uu____5859 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5859 in
                  let uu____5860 =
                    let uu____5865 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5865) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5856 uu____5860 in
                (match uu____5849 with
                 | (e2,uu____5879,g) ->
                     ((let uu____5882 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5882);
                      (let se1 =
                         let uu___379_5884 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___379_5884.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___379_5884.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___379_5884.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___379_5884.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5935 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5935
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5943 =
                      let uu____5944 =
                        let uu____5949 =
                          let uu____5950 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5951 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5952 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5950 uu____5951 uu____5952 in
                        (uu____5949, r) in
                      FStar_Errors.Error uu____5944 in
                    FStar_Exn.raise uu____5943) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5978 =
                   let uu____5979 = FStar_Syntax_Subst.compress def in
                   uu____5979.FStar_Syntax_Syntax.n in
                 match uu____5978 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5989,uu____5990)
                     -> binders
                 | uu____6011 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6021;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6099) -> val_bs1
                     | (uu____6122,[]) -> val_bs1
                     | ((body_bv,uu____6146)::bt,(val_bv,aqual)::vt) ->
                         let uu____6183 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6199) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___380_6201 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___381_6204 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___381_6204.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___380_6201.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___380_6201.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6183 in
                   let uu____6205 =
                     let uu____6208 =
                       let uu____6209 =
                         let uu____6222 = rename_binders1 def_bs val_bs in
                         (uu____6222, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6209 in
                     FStar_Syntax_Syntax.mk uu____6208 in
                   uu____6205 FStar_Pervasives_Native.None r1
               | uu____6240 -> typ1 in
             let uu___382_6241 = lb in
             let uu____6242 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___382_6241.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___382_6241.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6242;
               FStar_Syntax_Syntax.lbeff =
                 (uu___382_6241.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___382_6241.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____6245 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6296  ->
                     fun lb  ->
                       match uu____6296 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6338 =
                             let uu____6349 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6349 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____6434 ->
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
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let uu____6477 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6477, quals_opt1))) in
                           (match uu____6338 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6245 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6571 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___353_6575  ->
                                match uu___353_6575 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6576 -> false)) in
                      if uu____6571
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6586 =
                    let uu____6589 =
                      let uu____6590 =
                        let uu____6603 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6603) in
                      FStar_Syntax_Syntax.Tm_let uu____6590 in
                    FStar_Syntax_Syntax.mk uu____6589 in
                  uu____6586 FStar_Pervasives_Native.None r in
                let uu____6621 =
                  let uu____6632 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___383_6641 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___383_6641.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___383_6641.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___383_6641.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___383_6641.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___383_6641.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___383_6641.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___383_6641.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___383_6641.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___383_6641.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___383_6641.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___383_6641.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___383_6641.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___383_6641.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___383_6641.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___383_6641.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___383_6641.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___383_6641.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___383_6641.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___383_6641.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___383_6641.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___383_6641.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___383_6641.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___383_6641.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___383_6641.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___383_6641.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___383_6641.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___383_6641.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___383_6641.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___383_6641.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___383_6641.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___383_6641.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___383_6641.FStar_TypeChecker_Env.dep_graph)
                       }) e in
                  match uu____6632 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6654;
                       FStar_Syntax_Syntax.vars = uu____6655;_},uu____6656,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6685 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6685) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6703,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6708 -> quals in
                      ((let uu___384_6716 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___384_6716.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___384_6716.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___384_6716.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6725 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6621 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6774 = log env2 in
                       if uu____6774
                       then
                         let uu____6775 =
                           let uu____6776 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6791 =
                                         let uu____6800 =
                                           let uu____6801 =
                                             let uu____6804 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6804.FStar_Syntax_Syntax.fv_name in
                                           uu____6801.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6800 in
                                       match uu____6791 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6811 -> false in
                                     if should_log
                                     then
                                       let uu____6820 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6821 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6820 uu____6821
                                     else "")) in
                           FStar_All.pipe_right uu____6776
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6775
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6852 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6852 with
                              | (bs1,c1) ->
                                  let uu____6859 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6859
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6871 =
                                            let uu____6872 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6872.FStar_Syntax_Syntax.n in
                                          (match uu____6871 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6897 =
                                                 let uu____6898 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6898.FStar_Syntax_Syntax.n in
                                               (match uu____6897 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6908 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6908 in
                                                    let uu____6909 =
                                                      let uu____6910 =
                                                        let uu____6911 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6911 args in
                                                      uu____6910
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6909 u
                                                | uu____6914 -> c1)
                                           | uu____6915 -> c1)
                                      | uu____6916 -> c1 in
                                    let uu___385_6917 = t1 in
                                    let uu____6918 =
                                      let uu____6919 =
                                        let uu____6932 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6932) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6919 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6918;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___385_6917.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___385_6917.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6956 =
                               let uu____6957 = FStar_Syntax_Subst.compress h in
                               uu____6957.FStar_Syntax_Syntax.n in
                             (match uu____6956 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6967 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6967 in
                                  let uu____6968 =
                                    let uu____6969 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6969
                                      args in
                                  uu____6968 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6972 -> t1)
                         | uu____6973 -> t1 in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp in
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
                         } in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____7001 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____7001 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____7018 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____7018, (FStar_Pervasives_Native.snd x)))
                             bs in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.tac_effect_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let unit_binder =
                           let uu____7049 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____7049 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let uu___386_7056 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___387_7068 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___387_7068.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___387_7068.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___387_7068.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___387_7068.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___386_7056.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___386_7056.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___386_7056.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___386_7056.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7085 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____7085 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____7119 =
                                    let uu____7120 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____7120.FStar_Syntax_Syntax.n in
                                  (match uu____7119 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____7153 =
                                           let uu____7156 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____7156.FStar_Syntax_Syntax.fv_name in
                                         uu____7153.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____7158 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7158 in
                                       let uu____7159 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____7159 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7169 =
                                              let uu____7170 =
                                                let uu____7171 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7171 in
                                              Prims.op_Negation uu____7170 in
                                            if uu____7169
                                            then
                                              ((let uu____7201 =
                                                  let uu____7202 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____7202 in
                                                if uu____7201
                                                then
                                                  let added_modules =
                                                    FStar_ST.op_Bang
                                                      user_tactics_modules in
                                                  let module_name =
                                                    FStar_Ident.ml_path_of_lid
                                                      env2.FStar_TypeChecker_Env.curmodule in
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
                                                    assm_lid in
                                                if uu____7309
                                                then
                                                  let se_assm =
                                                    reified_tactic_decl
                                                      assm_lid hd1 in
                                                  let se_refl =
                                                    reflected_tactic_decl
                                                      (FStar_Pervasives_Native.fst
                                                         lbs1) hd1 bs
                                                      assm_lid comp in
                                                  FStar_Pervasives_Native.Some
                                                    (se_assm, se_refl)
                                                else
                                                  FStar_Pervasives_Native.None))
                                            else FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7338 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7343 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7365 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7365
                             then
                               let uu____7366 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7367 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7366 uu____7367
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___354_7418  ->
                match uu___354_7418 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7419 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7425) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7431 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7440 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7445 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7470 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7494) ->
          let uu____7503 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7503
          then
            let for_export_bundle se1 uu____7534 =
              match uu____7534 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7573,uu____7574) ->
                       let dec =
                         let uu___388_7584 = se1 in
                         let uu____7585 =
                           let uu____7586 =
                             let uu____7593 =
                               let uu____7596 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7596 in
                             (l, us, uu____7593) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7586 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7585;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___388_7584.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___388_7584.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___388_7584.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7608,uu____7609,uu____7610) ->
                       let dec =
                         let uu___389_7616 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___389_7616.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___389_7616.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___389_7616.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7621 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7643,uu____7644,uu____7645) ->
          let uu____7646 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7646 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7667 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7667
          then
            ([(let uu___390_7683 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___390_7683.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___390_7683.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___390_7683.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7685 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___355_7689  ->
                       match uu___355_7689 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7690 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7695 -> true
                       | uu____7696 -> false)) in
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
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7769 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
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
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7800 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7800
          then
            let uu____7809 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___391_7822 = se in
                      let uu____7823 =
                        let uu____7824 =
                          let uu____7831 =
                            let uu____7832 =
                              let uu____7835 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7835.FStar_Syntax_Syntax.fv_name in
                            uu____7832.FStar_Syntax_Syntax.v in
                          (uu____7831, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7824 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7823;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___391_7822.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___391_7822.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___391_7822.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7809, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
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
            let uu____7891 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7891 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7893 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7894 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7904 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7904) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7905,uu____7906,uu____7907) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___356_7911  ->
                  match uu___356_7911 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7912 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7913,uu____7914) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___356_7922  ->
                  match uu___356_7922 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7923 -> false))
          -> env
      | uu____7924 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7984 se =
        match uu____7984 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____8037 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____8037
              then
                let uu____8038 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8038
              else ());
             (let uu____8040 = tc_decl env1 se in
              match uu____8040 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____8090 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____8090
                             then
                               let uu____8091 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____8091
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
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
                              fun se1  -> add_sigelt_to_env env2 se1) env1) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____8114 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____8114
                     then
                       let uu____8115 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8121 =
                                  let uu____8122 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____8122 "\n" in
                                Prims.strcat s uu____8121) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____8115
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8127 =
                       let accum_exports_hidden uu____8157 se1 =
                         match uu____8157 with
                         | (exports1,hidden1) ->
                             let uu____8185 = for_export hidden1 se1 in
                             (match uu____8185 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____8127 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___392_8264 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___392_8264.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___392_8264.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___392_8264.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___392_8264.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8342 = acc in
        match uu____8342 with
        | (uu____8377,uu____8378,env1,uu____8380) ->
            let uu____8393 =
              FStar_Util.record_time
                (fun uu____8439  -> process_one_decl acc se) in
            (match uu____8393 with
             | (r,ms_elapsed) ->
                 ((let uu____8503 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8503
                   then
                     let uu____8504 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8505 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8504 uu____8505
                   else ());
                  r)) in
      let uu____8507 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8507 with
      | (ses1,exports,env1,uu____8555) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun push_before_typechecking  ->
        let verify =
          FStar_Options.should_verify
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
        let action = if verify then "Verifying" else "Lax-checking" in
        let label1 =
          if modul.FStar_Syntax_Syntax.is_interface
          then "interface"
          else "implementation" in
        (let uu____8595 = FStar_Options.debug_any () in
         if uu____8595
         then
           FStar_Util.print3 "%s %s of %s\n" action label1
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         else ());
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
         let msg = Prims.strcat "Internals for " name in
         let env1 =
           let uu___393_8601 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___393_8601.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___393_8601.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___393_8601.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___393_8601.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___393_8601.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___393_8601.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___393_8601.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___393_8601.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___393_8601.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___393_8601.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___393_8601.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___393_8601.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___393_8601.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___393_8601.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___393_8601.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___393_8601.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___393_8601.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___393_8601.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___393_8601.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___393_8601.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___393_8601.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___393_8601.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___393_8601.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___393_8601.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___393_8601.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___393_8601.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___393_8601.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___393_8601.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___393_8601.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___393_8601.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___393_8601.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___393_8601.FStar_TypeChecker_Env.dep_graph)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8605 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8605 with
          | (ses,exports,env3) ->
              ((let uu___394_8638 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___394_8638.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___394_8638.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___394_8638.FStar_Syntax_Syntax.is_interface)
                }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____8660 = tc_decls env decls in
        match uu____8660 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___395_8691 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___395_8691.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___395_8691.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___395_8691.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___396_8708 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___396_8708.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___396_8708.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___396_8708.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___396_8708.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___396_8708.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___396_8708.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___396_8708.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___396_8708.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___396_8708.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___396_8708.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___396_8708.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___396_8708.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___396_8708.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___396_8708.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___396_8708.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___396_8708.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___396_8708.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___396_8708.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___396_8708.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___396_8708.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___396_8708.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___396_8708.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___396_8708.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___396_8708.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___396_8708.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___396_8708.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___396_8708.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___396_8708.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___396_8708.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___396_8708.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___396_8708.FStar_TypeChecker_Env.dep_graph)
          } in
        let check_term1 lid univs1 t =
          let uu____8719 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8719 with
          | (univs2,t1) ->
              ((let uu____8727 =
                  let uu____8728 =
                    let uu____8731 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8731 in
                  FStar_All.pipe_left uu____8728
                    (FStar_Options.Other "Exports") in
                if uu____8727
                then
                  let uu____8732 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8733 =
                    let uu____8734 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8734
                      (FStar_String.concat ", ") in
                  let uu____8743 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8732 uu____8733 uu____8743
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8746 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8746 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8770 =
             let uu____8771 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8772 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8771 uu____8772 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8770);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8779) ->
              let uu____8788 =
                let uu____8789 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8789 in
              if uu____8788
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8799,uu____8800) ->
              let t =
                let uu____8812 =
                  let uu____8815 =
                    let uu____8816 =
                      let uu____8829 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8829) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8816 in
                  FStar_Syntax_Syntax.mk uu____8815 in
                uu____8812 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8836,uu____8837,uu____8838) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8846 =
                let uu____8847 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8847 in
              if uu____8846 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8851,lbs),uu____8853) ->
              let uu____8868 =
                let uu____8869 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8869 in
              if uu____8868
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term2
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags) ->
              let uu____8888 =
                let uu____8889 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8889 in
              if uu____8888
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8896 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8897 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8904 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8905 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8906 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8907 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let load_checked_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name in
      let env2 =
        FStar_List.fold_left FStar_TypeChecker_Env.push_sigelt env1
          modul.FStar_Syntax_Syntax.exports in
      let env3 = FStar_TypeChecker_Env.finish_module env2 modul in
      (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
        env3 modul;
      (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
      (let uu____8921 =
         let uu____8922 = FStar_Options.interactive () in
         Prims.op_Negation uu____8922 in
       if uu____8921
       then
         let uu____8923 = FStar_Options.restore_cmd_line_options true in
         FStar_All.pipe_right uu____8923 FStar_Pervasives.ignore
       else ());
      env3
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
          let uu___397_8939 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___397_8939.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___397_8939.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8942 =
           let uu____8943 = FStar_Options.lax () in
           Prims.op_Negation uu____8943 in
         if uu____8942 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8949 =
           let uu____8950 = FStar_Options.interactive () in
           Prims.op_Negation uu____8950 in
         if uu____8949
         then
           let uu____8951 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8951 FStar_Pervasives.ignore
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let uu____8963 = tc_partial_modul env modul true in
      match uu____8963 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      (let uu____8994 = FStar_Options.debug_any () in
       if uu____8994
       then
         let uu____8995 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8995
       else ());
      (let env1 =
         let uu___398_8999 = env in
         let uu____9000 =
           let uu____9001 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____9001 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___398_8999.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___398_8999.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___398_8999.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___398_8999.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___398_8999.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___398_8999.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___398_8999.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___398_8999.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___398_8999.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___398_8999.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___398_8999.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___398_8999.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___398_8999.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___398_8999.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___398_8999.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___398_8999.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___398_8999.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___398_8999.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____9000;
           FStar_TypeChecker_Env.lax_universes =
             (uu___398_8999.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___398_8999.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___398_8999.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___398_8999.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___398_8999.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___398_8999.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___398_8999.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___398_8999.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___398_8999.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___398_8999.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___398_8999.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___398_8999.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___398_8999.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___398_8999.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___398_8999.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____9002 = tc_modul env1 m in
       match uu____9002 with
       | (m1,env2) ->
           ((let uu____9014 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____9014
             then
               let uu____9015 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____9015
             else ());
            (let uu____9018 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____9018
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
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____9049 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____9049 with
                       | (univnames1,e) ->
                           let uu___399_9056 = lb in
                           let uu____9057 =
                             let uu____9060 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____9060 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___399_9056.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___399_9056.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___399_9056.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___399_9056.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9057
                           } in
                     let uu___400_9061 = se in
                     let uu____9062 =
                       let uu____9063 =
                         let uu____9070 =
                           let uu____9077 = FStar_List.map update lbs in
                           (b, uu____9077) in
                         (uu____9070, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____9063 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9062;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___400_9061.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___400_9061.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___400_9061.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___400_9061.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9090 -> se in
               let normalized_module =
                 let uu___401_9092 = m1 in
                 let uu____9093 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___401_9092.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9093;
                   FStar_Syntax_Syntax.exports =
                     (uu___401_9092.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___401_9092.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____9094 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____9094
             else ());
            (m1, env2)))