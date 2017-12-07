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
          let uu___300_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___300_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___300_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___300_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___300_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___300_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___300_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___300_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___300_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___300_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___300_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___300_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___300_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___300_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___300_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___300_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___300_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___300_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___300_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___300_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___300_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___300_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___300_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___300_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___300_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___300_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___300_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___300_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___300_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___300_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___300_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___300_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___300_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___300_13.FStar_TypeChecker_Env.dep_graph)
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
          let uu___301_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___301_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___301_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___301_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___301_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___301_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___301_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___301_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___301_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___301_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___301_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___301_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___301_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___301_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___301_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___301_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___301_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___301_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___301_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___301_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___301_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___301_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___301_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___301_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___301_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___301_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___301_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___301_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___301_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___301_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___301_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___301_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___301_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___301_29.FStar_TypeChecker_Env.dep_graph)
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
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          FStar_Errors.raise_error uu____233 (FStar_Ident.range_of_lid m) in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____277)::(wp,uu____279)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____294 -> fail ())
        | uu____295 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____302 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____302 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____328 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____328 t in
          let open_univs_binders n_binders bs =
            let uu____338 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____338 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____346 =
            let uu____353 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders in
            let uu____354 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____353 uu____354 in
          (match uu____346 with
           | (effect_params_un,signature_un,opening) ->
               let uu____364 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
               (match uu____364 with
                | (effect_params,env,uu____373) ->
                    let uu____374 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un in
                    (match uu____374 with
                     | (signature,uu____380) ->
                         let ed1 =
                           let uu___302_382 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___302_382.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___302_382.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___302_382.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___302_382.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___302_382.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___302_382.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___302_382.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___302_382.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___302_382.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___302_382.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___302_382.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___302_382.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___302_382.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___302_382.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___302_382.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___302_382.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___302_382.FStar_Syntax_Syntax.actions)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____398 ->
                               let op uu____420 =
                                 match uu____420 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____440 =
                                       let uu____441 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____450 =
                                         open_univs (n_effect_params + n_us)
                                           t in
                                       FStar_Syntax_Subst.subst uu____441
                                         uu____450 in
                                     (us, uu____440) in
                               let uu___303_463 = ed1 in
                               let uu____464 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____465 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____466 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____467 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____468 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____469 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____470 =
                                 op ed1.FStar_Syntax_Syntax.assert_p in
                               let uu____471 =
                                 op ed1.FStar_Syntax_Syntax.assume_p in
                               let uu____472 =
                                 op ed1.FStar_Syntax_Syntax.null_wp in
                               let uu____473 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____474 =
                                 let uu____475 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____475 in
                               let uu____486 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____487 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____488 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___304_496 = a in
                                      let uu____497 =
                                        let uu____498 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____498 in
                                      let uu____509 =
                                        let uu____510 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd uu____510 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___304_496.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___304_496.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___304_496.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___304_496.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____497;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____509
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___303_463.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___303_463.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___303_463.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___303_463.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____464;
                                 FStar_Syntax_Syntax.bind_wp = uu____465;
                                 FStar_Syntax_Syntax.if_then_else = uu____466;
                                 FStar_Syntax_Syntax.ite_wp = uu____467;
                                 FStar_Syntax_Syntax.stronger = uu____468;
                                 FStar_Syntax_Syntax.close_wp = uu____469;
                                 FStar_Syntax_Syntax.assert_p = uu____470;
                                 FStar_Syntax_Syntax.assume_p = uu____471;
                                 FStar_Syntax_Syntax.null_wp = uu____472;
                                 FStar_Syntax_Syntax.trivial = uu____473;
                                 FStar_Syntax_Syntax.repr = uu____474;
                                 FStar_Syntax_Syntax.return_repr = uu____486;
                                 FStar_Syntax_Syntax.bind_repr = uu____487;
                                 FStar_Syntax_Syntax.actions = uu____488
                               } in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____547 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t in
                             FStar_Errors.raise_error uu____547
                               (FStar_Ident.range_of_lid mname) in
                           let uu____558 =
                             let uu____559 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____559.FStar_Syntax_Syntax.n in
                           match uu____558 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a,uu____594)::(wp,uu____596)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____611 -> fail signature1)
                           | uu____612 -> fail signature1 in
                         let uu____613 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____613 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____635 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____642 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un in
                                    (match uu____642 with
                                     | (signature1,uu____654) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____655 ->
                                    let uu____658 =
                                      let uu____663 =
                                        let uu____664 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____664) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____663 in
                                    (match uu____658 with
                                     | (uu____673,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env1 =
                                let uu____676 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env uu____676 in
                              ((let uu____678 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____678
                                then
                                  let uu____679 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____680 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____681 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____682 =
                                    let uu____683 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____683 in
                                  let uu____684 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____679 uu____680 uu____681 uu____682
                                    uu____684
                                else ());
                               (let check_and_gen' env2 uu____700 k =
                                  match uu____700 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____714::uu____715 ->
                                           let uu____718 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____718 with
                                            | (us1,t1) ->
                                                let uu____727 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____727 with
                                                 | (us2,t2) ->
                                                     let uu____734 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k in
                                                     let uu____735 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____735)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____740 =
                                      let uu____747 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____748 =
                                        let uu____751 =
                                          let uu____752 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____752 in
                                        [uu____751] in
                                      uu____747 :: uu____748 in
                                    let uu____753 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____740
                                      uu____753 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____757 = fresh_effect_signature () in
                                  match uu____757 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____773 =
                                          let uu____780 =
                                            let uu____781 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____781 in
                                          [uu____780] in
                                        let uu____782 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____773
                                          uu____782 in
                                      let expected_k =
                                        let uu____788 =
                                          let uu____795 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____796 =
                                            let uu____799 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____800 =
                                              let uu____803 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____804 =
                                                let uu____807 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____808 =
                                                  let uu____811 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____811] in
                                                uu____807 :: uu____808 in
                                              uu____803 :: uu____804 in
                                            uu____799 :: uu____800 in
                                          uu____795 :: uu____796 in
                                        let uu____812 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____788
                                          uu____812 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____817 =
                                      let uu____818 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____818
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____817 in
                                  let expected_k =
                                    let uu____830 =
                                      let uu____837 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____838 =
                                        let uu____841 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____842 =
                                          let uu____845 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____846 =
                                            let uu____849 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____849] in
                                          uu____845 :: uu____846 in
                                        uu____841 :: uu____842 in
                                      uu____837 :: uu____838 in
                                    let uu____850 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____830
                                      uu____850 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____857 =
                                      let uu____864 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____865 =
                                        let uu____868 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____868] in
                                      uu____864 :: uu____865 in
                                    let uu____869 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____857
                                      uu____869 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____873 = FStar_Syntax_Util.type_u () in
                                  match uu____873 with
                                  | (t,uu____879) ->
                                      let expected_k =
                                        let uu____883 =
                                          let uu____890 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____891 =
                                            let uu____894 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____895 =
                                              let uu____898 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____898] in
                                            uu____894 :: uu____895 in
                                          uu____890 :: uu____891 in
                                        let uu____899 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____883
                                          uu____899 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____904 =
                                      let uu____905 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____905
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____904 in
                                  let b_wp_a =
                                    let uu____917 =
                                      let uu____924 =
                                        let uu____925 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____925 in
                                      [uu____924] in
                                    let uu____926 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____917
                                      uu____926 in
                                  let expected_k =
                                    let uu____932 =
                                      let uu____939 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____940 =
                                        let uu____943 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____944 =
                                          let uu____947 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____947] in
                                        uu____943 :: uu____944 in
                                      uu____939 :: uu____940 in
                                    let uu____948 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____932
                                      uu____948 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let assert_p =
                                  let expected_k =
                                    let uu____955 =
                                      let uu____962 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____963 =
                                        let uu____966 =
                                          let uu____967 =
                                            let uu____968 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____968
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____967 in
                                        let uu____977 =
                                          let uu____980 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____980] in
                                        uu____966 :: uu____977 in
                                      uu____962 :: uu____963 in
                                    let uu____981 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____955
                                      uu____981 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k in
                                let assume_p =
                                  let expected_k =
                                    let uu____988 =
                                      let uu____995 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____996 =
                                        let uu____999 =
                                          let uu____1000 =
                                            let uu____1001 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____1001
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1000 in
                                        let uu____1010 =
                                          let uu____1013 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1013] in
                                        uu____999 :: uu____1010 in
                                      uu____995 :: uu____996 in
                                    let uu____1014 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____988
                                      uu____1014 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k in
                                let null_wp =
                                  let expected_k =
                                    let uu____1021 =
                                      let uu____1028 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      [uu____1028] in
                                    let uu____1029 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1021
                                      uu____1029 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1033 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1033 with
                                  | (t,uu____1039) ->
                                      let expected_k =
                                        let uu____1043 =
                                          let uu____1050 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1051 =
                                            let uu____1054 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1054] in
                                          uu____1050 :: uu____1051 in
                                        let uu____1055 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1043
                                          uu____1055 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1058 =
                                  let uu____1069 =
                                    let uu____1070 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1070.FStar_Syntax_Syntax.n in
                                  match uu____1069 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1085 ->
                                      let repr =
                                        let uu____1087 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1087 with
                                        | (t,uu____1093) ->
                                            let expected_k =
                                              let uu____1097 =
                                                let uu____1104 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1105 =
                                                  let uu____1108 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1108] in
                                                uu____1104 :: uu____1105 in
                                              let uu____1109 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1097 uu____1109 in
                                            tc_check_trivial_guard env1
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env1 repr in
                                        let uu____1122 =
                                          let uu____1125 =
                                            let uu____1126 =
                                              let uu____1141 =
                                                let uu____1144 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1145 =
                                                  let uu____1148 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1148] in
                                                uu____1144 :: uu____1145 in
                                              (repr1, uu____1141) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1126 in
                                          FStar_Syntax_Syntax.mk uu____1125 in
                                        uu____1122
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1163 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1163 wp in
                                      let destruct_repr t =
                                        let uu____1176 =
                                          let uu____1177 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1177.FStar_Syntax_Syntax.n in
                                        match uu____1176 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1188,(t1,uu____1190)::
                                             (wp,uu____1192)::[])
                                            -> (t1, wp)
                                        | uu____1235 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____1246 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____1246
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____1247 =
                                          fresh_effect_signature () in
                                        match uu____1247 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1263 =
                                                let uu____1270 =
                                                  let uu____1271 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1271 in
                                                [uu____1270] in
                                              let uu____1272 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____1263 uu____1272 in
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
                                              let uu____1278 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1278 in
                                            let wp_g_x =
                                              let uu____1282 =
                                                let uu____1283 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____1284 =
                                                  let uu____1285 =
                                                    let uu____1286 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1286 in
                                                  [uu____1285] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1283 uu____1284 in
                                              uu____1282
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____1295 =
                                                  let uu____1296 =
                                                    let uu____1297 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____1297
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____1306 =
                                                    let uu____1307 =
                                                      let uu____1310 =
                                                        let uu____1313 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____1314 =
                                                          let uu____1317 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____1318 =
                                                            let uu____1321 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____1322 =
                                                              let uu____1325
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____1325] in
                                                            uu____1321 ::
                                                              uu____1322 in
                                                          uu____1317 ::
                                                            uu____1318 in
                                                        uu____1313 ::
                                                          uu____1314 in
                                                      r :: uu____1310 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1307 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1296 uu____1306 in
                                                uu____1295
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let expected_k =
                                              let uu____1331 =
                                                let uu____1338 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1339 =
                                                  let uu____1342 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____1343 =
                                                    let uu____1346 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____1347 =
                                                      let uu____1350 =
                                                        let uu____1351 =
                                                          let uu____1352 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____1352 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1351 in
                                                      let uu____1353 =
                                                        let uu____1356 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____1357 =
                                                          let uu____1360 =
                                                            let uu____1361 =
                                                              let uu____1362
                                                                =
                                                                let uu____1369
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____1369] in
                                                              let uu____1370
                                                                =
                                                                let uu____1373
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1373 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1362
                                                                uu____1370 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1361 in
                                                          [uu____1360] in
                                                        uu____1356 ::
                                                          uu____1357 in
                                                      uu____1350 ::
                                                        uu____1353 in
                                                    uu____1346 :: uu____1347 in
                                                  uu____1342 :: uu____1343 in
                                                uu____1338 :: uu____1339 in
                                              let uu____1374 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____1331 uu____1374 in
                                            let uu____1377 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k in
                                            (match uu____1377 with
                                             | (expected_k1,uu____1385,uu____1386)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env3 =
                                                   let uu___305_1391 = env2 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___305_1391.FStar_TypeChecker_Env.dep_graph)
                                                   } in
                                                 let br =
                                                   check_and_gen' env3
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____1401 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1401 in
                                        let res =
                                          let wp =
                                            let uu____1408 =
                                              let uu____1409 =
                                                let uu____1410 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____1410
                                                  FStar_Pervasives_Native.snd in
                                              let uu____1419 =
                                                let uu____1420 =
                                                  let uu____1423 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____1424 =
                                                    let uu____1427 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____1427] in
                                                  uu____1423 :: uu____1424 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1420 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1409 uu____1419 in
                                            uu____1408
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____1433 =
                                            let uu____1440 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1441 =
                                              let uu____1444 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____1444] in
                                            uu____1440 :: uu____1441 in
                                          let uu____1445 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____1433
                                            uu____1445 in
                                        let uu____1448 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k in
                                        match uu____1448 with
                                        | (expected_k1,uu____1462,uu____1463)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____1467 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____1467 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1488 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos)) in
                                      let actions =
                                        let check_action act =
                                          let uu____1513 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ in
                                          match uu____1513 with
                                          | (act_typ,uu____1521,g_t) ->
                                              let env' =
                                                let uu___306_1524 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___306_1524.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___306_1524.FStar_TypeChecker_Env.dep_graph)
                                                } in
                                              ((let uu____1526 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED") in
                                                if uu____1526
                                                then
                                                  let uu____1527 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn in
                                                  let uu____1528 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1527 uu____1528
                                                else ());
                                               (let uu____1530 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn in
                                                match uu____1530 with
                                                | (act_defn,uu____1538,g_a)
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
                                                    let uu____1542 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1 in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1570 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c in
                                                          (match uu____1570
                                                           with
                                                           | (bs1,uu____1580)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun in
                                                               let k =
                                                                 let uu____1587
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1587 in
                                                               let uu____1590
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k in
                                                               (match uu____1590
                                                                with
                                                                | (k1,uu____1602,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1604 ->
                                                          let uu____1605 =
                                                            let uu____1610 =
                                                              let uu____1611
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2 in
                                                              let uu____1612
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1611
                                                                uu____1612 in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1610) in
                                                          FStar_Errors.raise_error
                                                            uu____1605
                                                            act_defn1.FStar_Syntax_Syntax.pos in
                                                    (match uu____1542 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k in
                                                         ((let uu____1621 =
                                                             let uu____1622 =
                                                               let uu____1623
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1623 in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1622 in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1621);
                                                          (let act_typ2 =
                                                             let uu____1627 =
                                                               let uu____1628
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k in
                                                               uu____1628.FStar_Syntax_Syntax.n in
                                                             match uu____1627
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1651
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                 (match uu____1651
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1660
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____1660
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1682
                                                                    =
                                                                    let uu____1683
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1683] in
                                                                    let uu____1684
                                                                    =
                                                                    let uu____1693
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1693] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1682;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1684;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1694
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1694))
                                                             | uu____1697 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)" in
                                                           let uu____1700 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1 in
                                                           match uu____1700
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
                                                               let uu___307_1709
                                                                 = act in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___307_1709.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___307_1709.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___307_1709.FStar_Syntax_Syntax.action_params);
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
                                match uu____1058 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1733 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1733 in
                                    let uu____1736 =
                                      let uu____1743 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____1743 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1764 ->
                                               let uu____1767 =
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
                                               if uu____1767
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1781 =
                                                    let uu____1786 =
                                                      let uu____1787 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names) in
                                                      let uu____1788 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs) in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1787 uu____1788 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1786) in
                                                  FStar_Errors.raise_error
                                                    uu____1781
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                    (match uu____1736 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1802 =
                                             let uu____1807 =
                                               let uu____1808 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____1808.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____1807) in
                                           match uu____1802 with
                                           | ([],uu____1811) -> t
                                           | (uu____1822,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1823,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1841 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1854 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1854 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____1859 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1861 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____1861))
                                                && (m <> n1) in
                                            if uu____1859
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____1877 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____1878 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format3
                                                  "The effect combinator is %s (n=%s) (%s)"
                                                  error uu____1877 uu____1878 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____1886 =
                                             close1 (- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____1886 with
                                           | (univs2,defn) ->
                                               let uu____1893 =
                                                 close1
                                                   (- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____1893 with
                                                | (univs',typ) ->
                                                    let uu___308_1903 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___308_1903.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___308_1903.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___308_1903.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___309_1908 = ed2 in
                                           let uu____1909 =
                                             close1 (Prims.parse_int "0")
                                               return_wp in
                                           let uu____1910 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp in
                                           let uu____1911 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1 in
                                           let uu____1912 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp in
                                           let uu____1913 =
                                             close1 (Prims.parse_int "0")
                                               stronger in
                                           let uu____1914 =
                                             close1 (Prims.parse_int "1")
                                               close_wp in
                                           let uu____1915 =
                                             close1 (Prims.parse_int "0")
                                               assert_p in
                                           let uu____1916 =
                                             close1 (Prims.parse_int "0")
                                               assume_p in
                                           let uu____1917 =
                                             close1 (Prims.parse_int "0")
                                               null_wp in
                                           let uu____1918 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp in
                                           let uu____1919 =
                                             let uu____1920 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____1920 in
                                           let uu____1931 =
                                             close1 (Prims.parse_int "0")
                                               return_repr in
                                           let uu____1932 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr in
                                           let uu____1933 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___309_1908.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___309_1908.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1909;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1910;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1911;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1912;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1913;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1914;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1915;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1916;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1917;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1918;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1919;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1931;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1932;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1933
                                           } in
                                         ((let uu____1937 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____1937
                                           then
                                             let uu____1938 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____1938
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
      let uu____1956 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1956 with
      | (effect_binders_un,signature_un) ->
          let uu____1973 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1973 with
           | (effect_binders,env1,uu____1992) ->
               let uu____1993 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1993 with
                | (signature,uu____2009) ->
                    let raise_error1 uu____2021 =
                      match uu____2021 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2047  ->
                           match uu____2047 with
                           | (bv,qual) ->
                               let uu____2058 =
                                 let uu___310_2059 = bv in
                                 let uu____2060 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___310_2059.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___310_2059.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2060
                                 } in
                               (uu____2058, qual)) effect_binders in
                    let uu____2063 =
                      let uu____2070 =
                        let uu____2071 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2071.FStar_Syntax_Syntax.n in
                      match uu____2070 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____2081)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____2103 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature") in
                    (match uu____2063 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2127 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2127
                           then
                             let uu____2128 =
                               let uu____2131 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2131 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2128
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2165 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2165 with
                           | (t2,comp,uu____2178) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2185 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2185 with
                          | (repr,_comp) ->
                              ((let uu____2207 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2207
                                then
                                  let uu____2208 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2208
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____2214 =
                                    let uu____2215 =
                                      let uu____2216 =
                                        let uu____2231 =
                                          let uu____2238 =
                                            let uu____2243 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2244 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2243, uu____2244) in
                                          [uu____2238] in
                                        (wp_type1, uu____2231) in
                                      FStar_Syntax_Syntax.Tm_app uu____2216 in
                                    mk1 uu____2215 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2214 in
                                let effect_signature =
                                  let binders =
                                    let uu____2269 =
                                      let uu____2274 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2274) in
                                    let uu____2275 =
                                      let uu____2282 =
                                        let uu____2283 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2283
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2282] in
                                    uu____2269 :: uu____2275 in
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
                                  let uu____2346 = item in
                                  match uu____2346 with
                                  | (u_item,item1) ->
                                      let uu____2367 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2367 with
                                       | (item2,item_comp) ->
                                           ((let uu____2383 =
                                               let uu____2384 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2384 in
                                             if uu____2383
                                             then
                                               let uu____2385 =
                                                 let uu____2390 =
                                                   let uu____2391 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2392 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2391 uu____2392 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2390) in
                                               FStar_Errors.raise_err
                                                 uu____2385
                                             else ());
                                            (let uu____2394 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2394 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2414 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2414 with
                                | (dmff_env1,uu____2438,bind_wp,bind_elab) ->
                                    let uu____2441 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2441 with
                                     | (dmff_env2,uu____2465,return_wp,return_elab)
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
                                           let uu____2472 =
                                             let uu____2473 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2473.FStar_Syntax_Syntax.n in
                                           match uu____2472 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2517 =
                                                 let uu____2532 =
                                                   let uu____2537 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2537 in
                                                 match uu____2532 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2601 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2517 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2640 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2640 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2657 =
                                                          let uu____2658 =
                                                            let uu____2673 =
                                                              let uu____2680
                                                                =
                                                                let uu____2685
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2686
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2685,
                                                                  uu____2686) in
                                                              [uu____2680] in
                                                            (wp_type1,
                                                              uu____2673) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2658 in
                                                        mk1 uu____2657 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2701 =
                                                      let uu____2710 =
                                                        let uu____2711 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2711 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2710 in
                                                    (match uu____2701 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2730
                                                           =
                                                           let error_msg =
                                                             let uu____2732 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2732
                                                               (match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg) in
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
                                                                (let uu____2738
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
                                                                   uu____2738
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
                                                             let uu____2765 =
                                                               let uu____2766
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2767
                                                                 =
                                                                 let uu____2768
                                                                   =
                                                                   let uu____2775
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2775,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2768] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2766
                                                                 uu____2767 in
                                                             uu____2765
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2800 =
                                                             let uu____2801 =
                                                               let uu____2808
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2808] in
                                                             b11 ::
                                                               uu____2801 in
                                                           let uu____2813 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2800
                                                             uu____2813
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2814 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let return_wp1 =
                                           let uu____2816 =
                                             let uu____2817 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2817.FStar_Syntax_Syntax.n in
                                           match uu____2816 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2861 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2861
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2874 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let bind_wp1 =
                                           let uu____2876 =
                                             let uu____2877 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2877.FStar_Syntax_Syntax.n in
                                           match uu____2876 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2904 =
                                                 let uu____2905 =
                                                   let uu____2908 =
                                                     let uu____2909 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2909 in
                                                   [uu____2908] in
                                                 FStar_List.append uu____2905
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2904 body what
                                           | uu____2910 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind") in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2928 =
                                                let uu____2929 =
                                                  let uu____2930 =
                                                    let uu____2945 =
                                                      let uu____2946 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2946 in
                                                    (t, uu____2945) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2930 in
                                                mk1 uu____2929 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2928) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2976 = f a2 in
                                               [uu____2976]
                                           | x::xs ->
                                               let uu____2981 =
                                                 apply_last1 f xs in
                                               x :: uu____2981 in
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
                                           let uu____3001 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3001 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3031 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3031
                                                 then
                                                   let uu____3032 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3032
                                                 else ());
                                                (let uu____3034 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3034))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3043 =
                                                 let uu____3048 = mk_lid name in
                                                 let uu____3049 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3048 uu____3049 in
                                               (match uu____3043 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3053 =
                                                        let uu____3056 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____3056 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3053);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3195 =
                                             let uu____3198 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3199 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3198 :: uu____3199 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3195);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3339 =
                                               let uu____3342 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3343 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3342 :: uu____3343 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3339);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3480 =
                                                FStar_List.fold_left
                                                  (fun uu____3520  ->
                                                     fun action  ->
                                                       match uu____3520 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3541 =
                                                             let uu____3548 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3548
                                                               params_un in
                                                           (match uu____3541
                                                            with
                                                            | (action_params,env',uu____3557)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3577
                                                                     ->
                                                                    match uu____3577
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3588
                                                                    =
                                                                    let uu___311_3589
                                                                    = bv in
                                                                    let uu____3590
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___311_3589.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___311_3589.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3590
                                                                    } in
                                                                    (uu____3588,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3594
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3594
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
                                                                    uu____3624
                                                                    ->
                                                                    let uu____3625
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3625 in
                                                                    ((
                                                                    let uu____3629
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3629
                                                                    then
                                                                    let uu____3630
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3631
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3632
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3633
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3630
                                                                    uu____3631
                                                                    uu____3632
                                                                    uu____3633
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
                                                                    let uu____3637
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu___312_3641
                                                                    = action in
                                                                    let uu____3642
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3643
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___312_3641.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___312_3641.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___312_3641.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3642;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3643
                                                                    } in
                                                                    uu____3640
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3637))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3480 with
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
                                                      let uu____3676 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3677 =
                                                        let uu____3680 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3680] in
                                                      uu____3676 ::
                                                        uu____3677 in
                                                    let uu____3681 =
                                                      let uu____3682 =
                                                        let uu____3683 =
                                                          let uu____3684 =
                                                            let uu____3699 =
                                                              let uu____3706
                                                                =
                                                                let uu____3711
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3712
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3711,
                                                                  uu____3712) in
                                                              [uu____3706] in
                                                            (repr,
                                                              uu____3699) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3684 in
                                                        mk1 uu____3683 in
                                                      let uu____3727 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3682
                                                        uu____3727 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3681
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3730 =
                                                    let uu____3737 =
                                                      let uu____3738 =
                                                        let uu____3741 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3741 in
                                                      uu____3738.FStar_Syntax_Syntax.n in
                                                    match uu____3737 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3751)
                                                        ->
                                                        let uu____3780 =
                                                          let uu____3797 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3797
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3855 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3780
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3905 =
                                                               let uu____3906
                                                                 =
                                                                 let uu____3909
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3909 in
                                                               uu____3906.FStar_Syntax_Syntax.n in
                                                             (match uu____3905
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3934
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3934
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3947
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3972
                                                                     ->
                                                                    match uu____3972
                                                                    with
                                                                    | 
                                                                    (bv,uu____3978)
                                                                    ->
                                                                    let uu____3979
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3980
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3979
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3947
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
                                                                    let uu____4044
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4044 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4049
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4057
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4057 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____4062
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____4065
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____4062,
                                                                    uu____4065)))
                                                              | uu____4072 ->
                                                                  let uu____4073
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4079
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4079 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4078) in
                                                                  raise_error1
                                                                    uu____4073))
                                                    | uu____4086 ->
                                                        let uu____4087 =
                                                          let uu____4092 =
                                                            let uu____4093 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type1 in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____4093 in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____4092) in
                                                        raise_error1
                                                          uu____4087 in
                                                  (match uu____3730 with
                                                   | (pre,post) ->
                                                       ((let uu____4117 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____4119 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____4121 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___313_4123
                                                             = ed in
                                                           let uu____4124 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____4125 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____4126 =
                                                             let uu____4127 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____4127) in
                                                           let uu____4134 =
                                                             let uu____4135 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4135) in
                                                           let uu____4142 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____4143 =
                                                             let uu____4144 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4144) in
                                                           let uu____4151 =
                                                             let uu____4152 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4152) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4124;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4125;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4126;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4134;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___313_4123.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4142;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4143;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4151;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____4159 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4159
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4177
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4177
                                                               then
                                                                 let uu____4178
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4178
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
                                                                    let uu____4190
                                                                    =
                                                                    let uu____4193
                                                                    =
                                                                    let uu____4202
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4202) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4193 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4190;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4217
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4217
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4219
                                                                 =
                                                                 let uu____4222
                                                                   =
                                                                   let uu____4225
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4225 in
                                                                 FStar_List.append
                                                                   uu____4222
                                                                   sigelts' in
                                                               (uu____4219,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4303 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4303 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4336 = FStar_List.hd ses in
            uu____4336.FStar_Syntax_Syntax.sigrng in
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
           | uu____4341 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4346,uu____4347);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4349;
               FStar_Syntax_Syntax.sigattrs = uu____4350;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4354);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4356;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4357;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4361);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4363;
                 FStar_Syntax_Syntax.sigattrs = uu____4364;_}::[]
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
                 let uu____4429 =
                   let uu____4432 =
                     let uu____4433 =
                       let uu____4440 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4440, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4433 in
                   FStar_Syntax_Syntax.mk uu____4432 in
                 uu____4429 FStar_Pervasives_Native.None r1 in
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
                   let uu____4458 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4458 in
                 let hd1 =
                   let uu____4460 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4460 in
                 let tl1 =
                   let uu____4462 =
                     let uu____4463 =
                       let uu____4466 =
                         let uu____4467 =
                           let uu____4474 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4474, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4467 in
                       FStar_Syntax_Syntax.mk uu____4466 in
                     uu____4463 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4462 in
                 let res =
                   let uu____4483 =
                     let uu____4486 =
                       let uu____4487 =
                         let uu____4494 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4494,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4487 in
                     FStar_Syntax_Syntax.mk uu____4486 in
                   uu____4483 FStar_Pervasives_Native.None r2 in
                 let uu____4500 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4500 in
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
               let uu____4539 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4539;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4544 ->
               let err_msg =
                 let uu____4548 =
                   let uu____4549 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4549 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4548 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
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
            let uu____4574 = FStar_Syntax_Util.type_u () in
            match uu____4574 with
            | (k,uu____4580) ->
                let phi1 =
                  let uu____4582 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4582
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4584 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4584 with
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
          let uu____4626 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4626 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4659 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4659 FStar_List.flatten in
              ((let uu____4673 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4673
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
                          let uu____4684 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4694,uu____4695,uu____4696,uu____4697,uu____4698)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4707 -> failwith "Impossible!" in
                          match uu____4684 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4718 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4722,uu____4723,uu____4724,uu____4725,uu____4726)
                        -> lid
                    | uu____4735 -> failwith "Impossible" in
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
                  let uu____4753 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4753
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
                     let uu____4776 =
                       let uu____4779 =
                         let uu____4780 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4780;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4779 :: ses1 in
                     (uu____4776, data_ops_ses)) in
                (let uu____4790 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4824 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4849 ->
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
           let uu____4901 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4901 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4940 = FStar_Options.set_options t s in
             match uu____4940 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_FailToProcessPragma,
                     "Failed to process pragma: use 'fstar --help' to see which options are available")
                   r
             | FStar_Getopt.Error s1 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_FailToProcessPragma,
                     (Prims.strcat "Failed to process pragma: " s1)) r in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____4966 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4966 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4974 = cps_and_elaborate env1 ne in
           (match uu____4974 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___314_5011 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___314_5011.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___314_5011.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___314_5011.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___314_5011.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___315_5013 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___315_5013.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___315_5013.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___315_5013.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___315_5013.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___316_5021 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___316_5021.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___316_5021.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___316_5021.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___316_5021.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____5029 =
             let uu____5036 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5036 in
           (match uu____5029 with
            | (a,wp_a_src) ->
                let uu____5051 =
                  let uu____5058 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5058 in
                (match uu____5051 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5074 =
                         let uu____5077 =
                           let uu____5078 =
                             let uu____5085 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____5085) in
                           FStar_Syntax_Syntax.NT uu____5078 in
                         [uu____5077] in
                       FStar_Syntax_Subst.subst uu____5074 wp_b_tgt in
                     let expected_k =
                       let uu____5089 =
                         let uu____5096 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____5097 =
                           let uu____5100 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____5100] in
                         uu____5096 :: uu____5097 in
                       let uu____5101 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____5089 uu____5101 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5122 =
                           let uu____5127 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5127) in
                         let uu____5128 =
                           FStar_TypeChecker_Env.get_range env1 in
                         FStar_Errors.raise_error uu____5122 uu____5128 in
                       let uu____5131 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____5131 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____5163 =
                             let uu____5164 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____5164 in
                           if uu____5163
                           then no_reify eff_name
                           else
                             (let uu____5170 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____5171 =
                                let uu____5174 =
                                  let uu____5175 =
                                    let uu____5190 =
                                      let uu____5193 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5194 =
                                        let uu____5197 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5197] in
                                      uu____5193 :: uu____5194 in
                                    (repr, uu____5190) in
                                  FStar_Syntax_Syntax.Tm_app uu____5175 in
                                FStar_Syntax_Syntax.mk uu____5174 in
                              uu____5171 FStar_Pervasives_Native.None
                                uu____5170) in
                     let uu____5203 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5231,lift_wp)) ->
                           let uu____5255 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5255)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5281 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5281
                             then
                               let uu____5282 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5282
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange) in
                             let uu____5285 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5285 with
                             | (lift1,comp,uu____5300) ->
                                 let uu____5301 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5301 with
                                  | (uu____5314,lift_wp,lift_elab) ->
                                      let uu____5317 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5318 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5203 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___317_5359 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___317_5359.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___317_5359.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___317_5359.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___317_5359.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___317_5359.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___317_5359.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___317_5359.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___317_5359.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___317_5359.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___317_5359.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___317_5359.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___317_5359.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___317_5359.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___317_5359.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___317_5359.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___317_5359.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___317_5359.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___317_5359.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___317_5359.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___317_5359.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___317_5359.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___317_5359.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___317_5359.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___317_5359.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___317_5359.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___317_5359.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___317_5359.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___317_5359.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___317_5359.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___317_5359.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___317_5359.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___317_5359.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___317_5359.FStar_TypeChecker_Env.dep_graph)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5365,lift1)
                                ->
                                let uu____5377 =
                                  let uu____5384 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5384 in
                                (match uu____5377 with
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
                                         let uu____5408 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5409 =
                                           let uu____5412 =
                                             let uu____5413 =
                                               let uu____5428 =
                                                 let uu____5431 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5432 =
                                                   let uu____5435 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5435] in
                                                 uu____5431 :: uu____5432 in
                                               (lift_wp1, uu____5428) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5413 in
                                           FStar_Syntax_Syntax.mk uu____5412 in
                                         uu____5409
                                           FStar_Pervasives_Native.None
                                           uu____5408 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5444 =
                                         let uu____5451 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5452 =
                                           let uu____5455 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5456 =
                                             let uu____5459 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5459] in
                                           uu____5455 :: uu____5456 in
                                         uu____5451 :: uu____5452 in
                                       let uu____5460 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5444
                                         uu____5460 in
                                     let uu____5463 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5463 with
                                      | (expected_k2,uu____5473,uu____5474)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___318_5477 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___318_5477.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___318_5477.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___319_5479 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___319_5479.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___319_5479.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___319_5479.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___319_5479.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5498 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5498 with
            | (tps1,c1) ->
                let uu____5513 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5513 with
                 | (tps2,env3,us) ->
                     let uu____5531 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5531 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5552 =
                              let uu____5553 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5553 in
                            match uu____5552 with
                            | (uvs1,t) ->
                                let uu____5568 =
                                  let uu____5581 =
                                    let uu____5586 =
                                      let uu____5587 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5587.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5586) in
                                  match uu____5581 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5602,c4)) -> ([], c4)
                                  | (uu____5642,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5669 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5568 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5713 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5713 with
                                         | (uu____5718,t1) ->
                                             let uu____5720 =
                                               let uu____5725 =
                                                 let uu____5726 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     lid in
                                                 let uu____5727 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.length uvs1)
                                                     FStar_Util.string_of_int in
                                                 let uu____5728 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1 in
                                                 FStar_Util.format3
                                                   "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                   uu____5726 uu____5727
                                                   uu____5728 in
                                               (FStar_Errors.Fatal_TooManyUniverse,
                                                 uu____5725) in
                                             FStar_Errors.raise_error
                                               uu____5720 r)
                                      else ();
                                      (let se1 =
                                         let uu___320_5731 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags1));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___320_5731.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___320_5731.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___320_5731.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___320_5731.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5748,uu____5749,uu____5750) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___295_5754  ->
                   match uu___295_5754 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5755 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5760,uu____5761) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___295_5769  ->
                   match uu___295_5769 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5770 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5780 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5780
             then
               let uu____5781 =
                 let uu____5786 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid) in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5786) in
               FStar_Errors.raise_error uu____5781 r
             else ());
            (let uu____5788 =
               if uvs = []
               then
                 let uu____5789 =
                   let uu____5790 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5790 in
                 check_and_gen env2 t uu____5789
               else
                 (let uu____5796 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5796 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5804 =
                          let uu____5805 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5805 in
                        tc_check_trivial_guard env2 t1 uu____5804 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5811 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5811)) in
             match uu____5788 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___321_5827 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___321_5827.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___321_5827.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___321_5827.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___321_5827.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5837 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5837 with
            | (uu____5850,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5860 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5860 with
            | (e1,c,g1) ->
                let uu____5878 =
                  let uu____5885 =
                    let uu____5888 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5888 in
                  let uu____5889 =
                    let uu____5894 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5894) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5885 uu____5889 in
                (match uu____5878 with
                 | (e2,uu____5908,g) ->
                     ((let uu____5911 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5911);
                      (let se1 =
                         let uu___322_5913 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___322_5913.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___322_5913.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___322_5913.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___322_5913.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5964 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5964
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5972 =
                      let uu____5977 =
                        let uu____5978 = FStar_Syntax_Print.lid_to_string l in
                        let uu____5979 = FStar_Syntax_Print.quals_to_string q in
                        let uu____5980 =
                          FStar_Syntax_Print.quals_to_string q' in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____5978 uu____5979 uu____5980 in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____5977) in
                    FStar_Errors.raise_error uu____5972 r) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____6006 =
                   let uu____6007 = FStar_Syntax_Subst.compress def in
                   uu____6007.FStar_Syntax_Syntax.n in
                 match uu____6006 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6017,uu____6018)
                     -> binders
                 | uu____6039 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6049;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6127) -> val_bs1
                     | (uu____6150,[]) -> val_bs1
                     | ((body_bv,uu____6174)::bt,(val_bv,aqual)::vt) ->
                         let uu____6211 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6227) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___323_6229 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___324_6232 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___324_6232.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___323_6229.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___323_6229.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6211 in
                   let uu____6233 =
                     let uu____6236 =
                       let uu____6237 =
                         let uu____6250 = rename_binders1 def_bs val_bs in
                         (uu____6250, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6237 in
                     FStar_Syntax_Syntax.mk uu____6236 in
                   uu____6233 FStar_Pervasives_Native.None r1
               | uu____6268 -> typ1 in
             let uu___325_6269 = lb in
             let uu____6270 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___325_6269.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___325_6269.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6270;
               FStar_Syntax_Syntax.lbeff =
                 (uu___325_6269.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___325_6269.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____6273 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6324  ->
                     fun lb  ->
                       match uu____6324 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6366 =
                             let uu____6377 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6377 with
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
                                   | uu____6462 ->
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
                                  (let uu____6505 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6505, quals_opt1))) in
                           (match uu____6366 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6273 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6599 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___296_6603  ->
                                match uu___296_6603 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6604 -> false)) in
                      if uu____6599
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6614 =
                    let uu____6617 =
                      let uu____6618 =
                        let uu____6631 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6631) in
                      FStar_Syntax_Syntax.Tm_let uu____6618 in
                    FStar_Syntax_Syntax.mk uu____6617 in
                  uu____6614 FStar_Pervasives_Native.None r in
                let uu____6649 =
                  let uu____6660 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___326_6669 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___326_6669.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___326_6669.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___326_6669.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___326_6669.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___326_6669.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___326_6669.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___326_6669.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___326_6669.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___326_6669.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___326_6669.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___326_6669.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___326_6669.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___326_6669.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___326_6669.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___326_6669.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___326_6669.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___326_6669.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___326_6669.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___326_6669.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___326_6669.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___326_6669.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___326_6669.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___326_6669.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___326_6669.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___326_6669.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___326_6669.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___326_6669.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___326_6669.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___326_6669.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___326_6669.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___326_6669.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___326_6669.FStar_TypeChecker_Env.dep_graph)
                       }) e in
                  match uu____6660 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6682;
                       FStar_Syntax_Syntax.vars = uu____6683;_},uu____6684,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6713 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6713) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6731,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6736 -> quals in
                      ((let uu___327_6744 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___327_6744.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___327_6744.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___327_6744.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6753 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6649 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6802 = log env2 in
                       if uu____6802
                       then
                         let uu____6803 =
                           let uu____6804 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6819 =
                                         let uu____6828 =
                                           let uu____6829 =
                                             let uu____6832 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6832.FStar_Syntax_Syntax.fv_name in
                                           uu____6829.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6828 in
                                       match uu____6819 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6839 -> false in
                                     if should_log
                                     then
                                       let uu____6848 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6849 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6848 uu____6849
                                     else "")) in
                           FStar_All.pipe_right uu____6804
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6803
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6880 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6880 with
                              | (bs1,c1) ->
                                  let uu____6887 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6887
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6899 =
                                            let uu____6900 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6900.FStar_Syntax_Syntax.n in
                                          (match uu____6899 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6925 =
                                                 let uu____6926 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6926.FStar_Syntax_Syntax.n in
                                               (match uu____6925 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6936 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6936 in
                                                    let uu____6937 =
                                                      let uu____6938 =
                                                        let uu____6939 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6939 args in
                                                      uu____6938
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6937 u
                                                | uu____6942 -> c1)
                                           | uu____6943 -> c1)
                                      | uu____6944 -> c1 in
                                    let uu___328_6945 = t1 in
                                    let uu____6946 =
                                      let uu____6947 =
                                        let uu____6960 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6960) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6947 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6946;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___328_6945.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___328_6945.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6984 =
                               let uu____6985 = FStar_Syntax_Subst.compress h in
                               uu____6985.FStar_Syntax_Syntax.n in
                             (match uu____6984 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6995 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6995 in
                                  let uu____6996 =
                                    let uu____6997 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6997
                                      args in
                                  uu____6996 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____7000 -> t1)
                         | uu____7001 -> t1 in
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
                           let uu____7029 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____7029 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____7046 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____7046, (FStar_Pervasives_Native.snd x)))
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
                           let uu____7077 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____7077 in
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
                         let uu___329_7084 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___330_7096 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___330_7096.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___330_7096.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___330_7096.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___330_7096.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___329_7084.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___329_7084.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___329_7084.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___329_7084.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____7113 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____7113 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____7147 =
                                    let uu____7148 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____7148.FStar_Syntax_Syntax.n in
                                  (match uu____7147 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____7181 =
                                           let uu____7184 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____7184.FStar_Syntax_Syntax.fv_name in
                                         uu____7181.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____7186 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7186 in
                                       let uu____7187 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____7187 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7197 =
                                              let uu____7198 =
                                                let uu____7199 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7199 in
                                              Prims.op_Negation uu____7198 in
                                            if uu____7197
                                            then
                                              ((let uu____7229 =
                                                  let uu____7230 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____7230 in
                                                if uu____7229
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
                                               (let uu____7341 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid in
                                                if uu____7341
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
                                   | uu____7370 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7375 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7397 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7397
                             then
                               let uu____7398 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7399 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7398 uu____7399
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
             (fun uu___297_7450  ->
                match uu___297_7450 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7451 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7457) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7463 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7472 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7477 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7502 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7526) ->
          let uu____7535 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7535
          then
            let for_export_bundle se1 uu____7566 =
              match uu____7566 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7605,uu____7606) ->
                       let dec =
                         let uu___331_7616 = se1 in
                         let uu____7617 =
                           let uu____7618 =
                             let uu____7625 =
                               let uu____7628 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7628 in
                             (l, us, uu____7625) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7618 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7617;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___331_7616.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___331_7616.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___331_7616.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7640,uu____7641,uu____7642) ->
                       let dec =
                         let uu___332_7648 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___332_7648.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___332_7648.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___332_7648.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7653 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7675,uu____7676,uu____7677) ->
          let uu____7678 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7678 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7699 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7699
          then
            ([(let uu___333_7715 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___333_7715.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___333_7715.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___333_7715.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7717 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___298_7721  ->
                       match uu___298_7721 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7722 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7727 -> true
                       | uu____7728 -> false)) in
             if uu____7717 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7746 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7751 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7756 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7761 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7766 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7784) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7801 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7801
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
          let uu____7832 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7832
          then
            let uu____7841 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___334_7854 = se in
                      let uu____7855 =
                        let uu____7856 =
                          let uu____7863 =
                            let uu____7864 =
                              let uu____7867 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7867.FStar_Syntax_Syntax.fv_name in
                            uu____7864.FStar_Syntax_Syntax.v in
                          (uu____7863, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7856 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7855;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___334_7854.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___334_7854.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___334_7854.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7841, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7887 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7904 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7919) ->
          let env1 =
            let uu____7923 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7923 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7925 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7926 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7936 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7936) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7937,uu____7938,uu____7939) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___299_7943  ->
                  match uu___299_7943 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7944 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7945,uu____7946) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___299_7954  ->
                  match uu___299_7954 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7955 -> false))
          -> env
      | uu____7956 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____8016 se =
        match uu____8016 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____8069 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____8069
              then
                let uu____8070 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8070
              else ());
             (let uu____8072 = tc_decl env1 se in
              match uu____8072 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____8122 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____8122
                             then
                               let uu____8123 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____8123
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
                    (let uu____8146 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____8146
                     then
                       let uu____8147 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____8153 =
                                  let uu____8154 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____8154 "\n" in
                                Prims.strcat s uu____8153) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____8147
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____8159 =
                       let accum_exports_hidden uu____8189 se1 =
                         match uu____8189 with
                         | (exports1,hidden1) ->
                             let uu____8217 = for_export hidden1 se1 in
                             (match uu____8217 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____8159 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___335_8296 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___335_8296.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___335_8296.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___335_8296.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___335_8296.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8374 = acc in
        match uu____8374 with
        | (uu____8409,uu____8410,env1,uu____8412) ->
            let uu____8425 =
              FStar_Util.record_time
                (fun uu____8471  -> process_one_decl acc se) in
            (match uu____8425 with
             | (r,ms_elapsed) ->
                 ((let uu____8535 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8535
                   then
                     let uu____8536 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8537 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8536 uu____8537
                   else ());
                  r)) in
      let uu____8539 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8539 with
      | (ses1,exports,env1,uu____8587) ->
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
        (let uu____8627 = FStar_Options.debug_any () in
         if uu____8627
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
           let uu___336_8633 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___336_8633.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___336_8633.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___336_8633.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___336_8633.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___336_8633.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___336_8633.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___336_8633.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___336_8633.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___336_8633.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___336_8633.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___336_8633.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___336_8633.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___336_8633.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___336_8633.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___336_8633.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___336_8633.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___336_8633.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___336_8633.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___336_8633.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___336_8633.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___336_8633.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___336_8633.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___336_8633.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___336_8633.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___336_8633.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___336_8633.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___336_8633.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___336_8633.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___336_8633.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___336_8633.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___336_8633.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___336_8633.FStar_TypeChecker_Env.dep_graph)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8637 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8637 with
          | (ses,exports,env3) ->
              ((let uu___337_8670 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___337_8670.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___337_8670.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___337_8670.FStar_Syntax_Syntax.is_interface)
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
        let uu____8692 = tc_decls env decls in
        match uu____8692 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___338_8723 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___338_8723.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___338_8723.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___338_8723.FStar_Syntax_Syntax.is_interface)
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
          let uu___339_8740 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___339_8740.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___339_8740.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___339_8740.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___339_8740.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___339_8740.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___339_8740.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___339_8740.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___339_8740.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___339_8740.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___339_8740.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___339_8740.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___339_8740.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___339_8740.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___339_8740.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___339_8740.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___339_8740.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___339_8740.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___339_8740.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___339_8740.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___339_8740.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___339_8740.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___339_8740.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___339_8740.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___339_8740.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___339_8740.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___339_8740.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___339_8740.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___339_8740.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___339_8740.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___339_8740.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___339_8740.FStar_TypeChecker_Env.dep_graph)
          } in
        let check_term1 lid univs1 t =
          let uu____8751 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8751 with
          | (univs2,t1) ->
              ((let uu____8759 =
                  let uu____8760 =
                    let uu____8763 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8763 in
                  FStar_All.pipe_left uu____8760
                    (FStar_Options.Other "Exports") in
                if uu____8759
                then
                  let uu____8764 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8765 =
                    let uu____8766 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8766
                      (FStar_String.concat ", ") in
                  let uu____8775 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8764 uu____8765 uu____8775
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8778 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8778 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8802 =
             let uu____8803 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8804 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8803 uu____8804 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8802);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8811) ->
              let uu____8820 =
                let uu____8821 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8821 in
              if uu____8820
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8831,uu____8832) ->
              let t =
                let uu____8844 =
                  let uu____8847 =
                    let uu____8848 =
                      let uu____8861 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8861) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8848 in
                  FStar_Syntax_Syntax.mk uu____8847 in
                uu____8844 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8868,uu____8869,uu____8870) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8878 =
                let uu____8879 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8879 in
              if uu____8878 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8883,lbs),uu____8885) ->
              let uu____8900 =
                let uu____8901 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8901 in
              if uu____8900
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
              (l,univs1,binders,comp,flags1) ->
              let uu____8920 =
                let uu____8921 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8921 in
              if uu____8920
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8928 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8929 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8936 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8937 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8938 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8939 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelts ->
          (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun must_check_exports  ->
    fun env  ->
      fun modul  ->
        fun exports  ->
          let modul1 =
            let uu___340_8958 = modul in
            {
              FStar_Syntax_Syntax.name =
                (uu___340_8958.FStar_Syntax_Syntax.name);
              FStar_Syntax_Syntax.declarations =
                (uu___340_8958.FStar_Syntax_Syntax.declarations);
              FStar_Syntax_Syntax.exports = exports;
              FStar_Syntax_Syntax.is_interface =
                (modul.FStar_Syntax_Syntax.is_interface)
            } in
          let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
          (let uu____8961 =
             (let uu____8964 = FStar_Options.lax () in
              Prims.op_Negation uu____8964) && must_check_exports in
           if uu____8961 then check_exports env1 modul1 exports else ());
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
            (Prims.strcat "Ending modul "
               (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
            env1 modul1;
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
            ();
          (let uu____8970 =
             let uu____8971 = FStar_Options.interactive () in
             Prims.op_Negation uu____8971 in
           if uu____8970
           then
             let uu____8972 = FStar_Options.restore_cmd_line_options true in
             FStar_All.pipe_right uu____8972 FStar_Pervasives.ignore
           else ());
          (modul1, env1)
let load_checked_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name in
      (let uu____8982 =
         let uu____8983 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         Prims.strcat "Internals for " uu____8983 in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____8982);
      (let env2 =
         FStar_List.fold_left
           (fun env2  ->
              fun se  ->
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se in
                let lids = FStar_Syntax_Util.lids_of_sigelt se in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____9002 =
                          FStar_TypeChecker_Env.try_lookup_lid env3 lid in
                        ()));
                env3) env1 modul.FStar_Syntax_Syntax.declarations in
       let uu____9023 =
         finish_partial_modul false env2 modul
           modul.FStar_Syntax_Syntax.exports in
       FStar_Pervasives_Native.snd uu____9023)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let uu____9038 = tc_partial_modul env modul true in
      match uu____9038 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul true env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      (let uu____9069 = FStar_Options.debug_any () in
       if uu____9069
       then
         let uu____9070 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____9070
       else ());
      (let env1 =
         let uu___341_9074 = env in
         let uu____9075 =
           let uu____9076 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____9076 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___341_9074.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___341_9074.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___341_9074.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___341_9074.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___341_9074.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___341_9074.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___341_9074.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___341_9074.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___341_9074.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___341_9074.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___341_9074.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___341_9074.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___341_9074.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___341_9074.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___341_9074.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___341_9074.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___341_9074.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___341_9074.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____9075;
           FStar_TypeChecker_Env.lax_universes =
             (uu___341_9074.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___341_9074.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___341_9074.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___341_9074.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___341_9074.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___341_9074.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___341_9074.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___341_9074.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___341_9074.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___341_9074.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___341_9074.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___341_9074.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___341_9074.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___341_9074.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___341_9074.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____9077 = tc_modul env1 m in
       match uu____9077 with
       | (m1,env2) ->
           ((let uu____9089 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____9089
             then
               let uu____9090 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____9090
             else ());
            (let uu____9093 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____9093
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
                       let uu____9124 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____9124 with
                       | (univnames1,e) ->
                           let uu___342_9131 = lb in
                           let uu____9132 =
                             let uu____9135 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____9135 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___342_9131.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___342_9131.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___342_9131.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___342_9131.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9132
                           } in
                     let uu___343_9136 = se in
                     let uu____9137 =
                       let uu____9138 =
                         let uu____9145 =
                           let uu____9152 = FStar_List.map update lbs in
                           (b, uu____9152) in
                         (uu____9145, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____9138 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9137;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___343_9136.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___343_9136.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___343_9136.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___343_9136.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9165 -> se in
               let normalized_module =
                 let uu___344_9167 = m1 in
                 let uu____9168 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___344_9167.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9168;
                   FStar_Syntax_Syntax.exports =
                     (uu___344_9167.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___344_9167.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____9169 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____9169
             else ());
            (m1, env2)))