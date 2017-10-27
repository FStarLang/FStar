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
          let uu___356_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___356_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___356_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___356_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___356_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___356_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___356_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___356_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___356_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___356_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___356_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___356_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___356_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___356_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___356_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___356_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___356_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___356_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___356_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___356_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___356_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___356_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___356_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___356_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___356_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___356_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___356_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___356_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___356_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___356_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___356_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___356_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___356_13.FStar_TypeChecker_Env.dsenv)
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
          let uu___357_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___357_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___357_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___357_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___357_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___357_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___357_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___357_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___357_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___357_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___357_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___357_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___357_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___357_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___357_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___357_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___357_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___357_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___357_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___357_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___357_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___357_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___357_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___357_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___357_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___357_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___357_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___357_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___357_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___357_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___357_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___357_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___357_29.FStar_TypeChecker_Env.dsenv)
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
      let uu____307 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____307 with
      | (effect_params_un,signature_un,opening) ->
          let uu____317 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____317 with
           | (effect_params,env,uu____326) ->
               let uu____327 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____327 with
                | (signature,uu____333) ->
                    let ed1 =
                      let uu___358_335 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___358_335.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___358_335.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___358_335.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___358_335.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___358_335.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___358_335.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___358_335.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___358_335.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___358_335.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___358_335.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___358_335.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___358_335.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___358_335.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___358_335.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___358_335.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___358_335.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___358_335.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____341 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___359_372 = ed1 in
                          let uu____373 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____374 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____375 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____376 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____377 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____378 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____379 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____380 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____381 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____382 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____383 =
                            let uu____384 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____384 in
                          let uu____395 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____396 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____397 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___360_405 = a in
                                 let uu____406 =
                                   let uu____407 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____407 in
                                 let uu____418 =
                                   let uu____419 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____419 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___360_405.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___360_405.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___360_405.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___360_405.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____406;
                                   FStar_Syntax_Syntax.action_typ = uu____418
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___359_372.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___359_372.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___359_372.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___359_372.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___359_372.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____373;
                            FStar_Syntax_Syntax.bind_wp = uu____374;
                            FStar_Syntax_Syntax.if_then_else = uu____375;
                            FStar_Syntax_Syntax.ite_wp = uu____376;
                            FStar_Syntax_Syntax.stronger = uu____377;
                            FStar_Syntax_Syntax.close_wp = uu____378;
                            FStar_Syntax_Syntax.assert_p = uu____379;
                            FStar_Syntax_Syntax.assume_p = uu____380;
                            FStar_Syntax_Syntax.null_wp = uu____381;
                            FStar_Syntax_Syntax.trivial = uu____382;
                            FStar_Syntax_Syntax.repr = uu____383;
                            FStar_Syntax_Syntax.return_repr = uu____395;
                            FStar_Syntax_Syntax.bind_repr = uu____396;
                            FStar_Syntax_Syntax.actions = uu____397
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____456 =
                          let uu____457 =
                            let uu____462 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____462, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____457 in
                        FStar_Exn.raise uu____456 in
                      let uu____469 =
                        let uu____470 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____470.FStar_Syntax_Syntax.n in
                      match uu____469 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____505)::(wp,uu____507)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____522 -> fail signature1)
                      | uu____523 -> fail signature1 in
                    let uu____524 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____524 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____546 =
                           let uu____547 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____547 with
                           | (signature1,uu____559) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____561 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____561 in
                         ((let uu____563 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____563
                           then
                             let uu____564 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____565 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____566 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____567 =
                               let uu____568 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____568 in
                             let uu____569 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____564 uu____565 uu____566 uu____567
                               uu____569
                           else ());
                          (let check_and_gen' env2 uu____585 k =
                             match uu____585 with
                             | (uu____593,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____603 =
                                 let uu____610 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____611 =
                                   let uu____614 =
                                     let uu____615 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____615 in
                                   [uu____614] in
                                 uu____610 :: uu____611 in
                               let uu____616 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____603 uu____616 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____620 = fresh_effect_signature () in
                             match uu____620 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____636 =
                                     let uu____643 =
                                       let uu____644 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____644 in
                                     [uu____643] in
                                   let uu____645 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____636
                                     uu____645 in
                                 let expected_k =
                                   let uu____651 =
                                     let uu____658 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_range in
                                     let uu____659 =
                                       let uu____662 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____663 =
                                         let uu____666 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____667 =
                                           let uu____670 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____671 =
                                             let uu____674 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____674] in
                                           uu____670 :: uu____671 in
                                         uu____666 :: uu____667 in
                                       uu____662 :: uu____663 in
                                     uu____658 :: uu____659 in
                                   let uu____675 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____651
                                     uu____675 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____680 =
                                 let uu____681 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____681
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____680 in
                             let expected_k =
                               let uu____693 =
                                 let uu____700 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____701 =
                                   let uu____704 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____705 =
                                     let uu____708 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____709 =
                                       let uu____712 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____712] in
                                     uu____708 :: uu____709 in
                                   uu____704 :: uu____705 in
                                 uu____700 :: uu____701 in
                               let uu____713 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____693 uu____713 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____720 =
                                 let uu____727 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____728 =
                                   let uu____731 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____731] in
                                 uu____727 :: uu____728 in
                               let uu____732 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____720 uu____732 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____736 = FStar_Syntax_Util.type_u () in
                             match uu____736 with
                             | (t,uu____742) ->
                                 let expected_k =
                                   let uu____746 =
                                     let uu____753 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____754 =
                                       let uu____757 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____758 =
                                         let uu____761 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____761] in
                                       uu____757 :: uu____758 in
                                     uu____753 :: uu____754 in
                                   let uu____762 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____746
                                     uu____762 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____767 =
                                 let uu____768 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____768
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____767 in
                             let b_wp_a =
                               let uu____780 =
                                 let uu____787 =
                                   let uu____788 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____788 in
                                 [uu____787] in
                               let uu____789 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____780 uu____789 in
                             let expected_k =
                               let uu____795 =
                                 let uu____802 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____803 =
                                   let uu____806 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____807 =
                                     let uu____810 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____810] in
                                   uu____806 :: uu____807 in
                                 uu____802 :: uu____803 in
                               let uu____811 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____795 uu____811 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____818 =
                                 let uu____825 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____826 =
                                   let uu____829 =
                                     let uu____830 =
                                       let uu____831 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____831
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____830 in
                                   let uu____840 =
                                     let uu____843 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____843] in
                                   uu____829 :: uu____840 in
                                 uu____825 :: uu____826 in
                               let uu____844 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____818 uu____844 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____851 =
                                 let uu____858 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____859 =
                                   let uu____862 =
                                     let uu____863 =
                                       let uu____864 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____864
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____863 in
                                   let uu____873 =
                                     let uu____876 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____876] in
                                   uu____862 :: uu____873 in
                                 uu____858 :: uu____859 in
                               let uu____877 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____851 uu____877 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____884 =
                                 let uu____891 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____891] in
                               let uu____892 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____884 uu____892 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____896 = FStar_Syntax_Util.type_u () in
                             match uu____896 with
                             | (t,uu____902) ->
                                 let expected_k =
                                   let uu____906 =
                                     let uu____913 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____914 =
                                       let uu____917 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____917] in
                                     uu____913 :: uu____914 in
                                   let uu____918 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____906
                                     uu____918 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____921 =
                             let uu____932 =
                               let uu____933 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____933.FStar_Syntax_Syntax.n in
                             match uu____932 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____948 ->
                                 let repr =
                                   let uu____950 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____950 with
                                   | (t,uu____956) ->
                                       let expected_k =
                                         let uu____960 =
                                           let uu____967 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____968 =
                                             let uu____971 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____971] in
                                           uu____967 :: uu____968 in
                                         let uu____972 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____960
                                           uu____972 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____985 =
                                     let uu____988 =
                                       let uu____989 =
                                         let uu____1004 =
                                           let uu____1007 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____1008 =
                                             let uu____1011 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____1011] in
                                           uu____1007 :: uu____1008 in
                                         (repr1, uu____1004) in
                                       FStar_Syntax_Syntax.Tm_app uu____989 in
                                     FStar_Syntax_Syntax.mk uu____988 in
                                   uu____985 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____1026 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____1026 wp in
                                 let destruct_repr t =
                                   let uu____1039 =
                                     let uu____1040 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____1040.FStar_Syntax_Syntax.n in
                                   match uu____1039 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1051,(t1,uu____1053)::(wp,uu____1055)::[])
                                       -> (t1, wp)
                                   | uu____1098 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____1109 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____1109
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____1110 = fresh_effect_signature () in
                                   match uu____1110 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1126 =
                                           let uu____1133 =
                                             let uu____1134 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1134 in
                                           [uu____1133] in
                                         let uu____1135 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____1126
                                           uu____1135 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____1141 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____1141 in
                                       let wp_g_x =
                                         let uu____1145 =
                                           let uu____1146 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____1147 =
                                             let uu____1148 =
                                               let uu____1149 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1149 in
                                             [uu____1148] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1146 uu____1147 in
                                         uu____1145
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____1158 =
                                             let uu____1159 =
                                               let uu____1160 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right
                                                 uu____1160
                                                 FStar_Pervasives_Native.snd in
                                             let uu____1169 =
                                               let uu____1170 =
                                                 let uu____1173 =
                                                   let uu____1176 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1177 =
                                                     let uu____1180 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1181 =
                                                       let uu____1184 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1185 =
                                                         let uu____1188 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1188] in
                                                       uu____1184 ::
                                                         uu____1185 in
                                                     uu____1180 :: uu____1181 in
                                                   uu____1176 :: uu____1177 in
                                                 r :: uu____1173 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1170 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1159 uu____1169 in
                                           uu____1158
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1194 =
                                           let uu____1201 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1202 =
                                             let uu____1205 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1206 =
                                               let uu____1209 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1210 =
                                                 let uu____1213 =
                                                   let uu____1214 =
                                                     let uu____1215 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1215 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1214 in
                                                 let uu____1216 =
                                                   let uu____1219 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1220 =
                                                     let uu____1223 =
                                                       let uu____1224 =
                                                         let uu____1225 =
                                                           let uu____1232 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1232] in
                                                         let uu____1233 =
                                                           let uu____1236 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1236 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1225
                                                           uu____1233 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1224 in
                                                     [uu____1223] in
                                                   uu____1219 :: uu____1220 in
                                                 uu____1213 :: uu____1216 in
                                               uu____1209 :: uu____1210 in
                                             uu____1205 :: uu____1206 in
                                           uu____1201 :: uu____1202 in
                                         let uu____1237 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1194
                                           uu____1237 in
                                       let uu____1240 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____1240 with
                                        | (expected_k1,uu____1248,uu____1249)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___361_1254 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___361_1254.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___361_1254.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___361_1254.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.failhard
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.failhard);
                                                FStar_TypeChecker_Env.nosynth
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.nosynth);
                                                FStar_TypeChecker_Env.tc_term
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.tc_term);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___361_1254.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.is_native_tactic);
                                                FStar_TypeChecker_Env.identifier_info
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.identifier_info);
                                                FStar_TypeChecker_Env.tc_hooks
                                                  =
                                                  (uu___361_1254.FStar_TypeChecker_Env.tc_hooks);
                                                FStar_TypeChecker_Env.dsenv =
                                                  (uu___361_1254.FStar_TypeChecker_Env.dsenv)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1264 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None
                                       uu____1264 in
                                   let res =
                                     let wp =
                                       let uu____1271 =
                                         let uu____1272 =
                                           let uu____1273 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1273
                                             FStar_Pervasives_Native.snd in
                                         let uu____1282 =
                                           let uu____1283 =
                                             let uu____1286 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1287 =
                                               let uu____1290 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1290] in
                                             uu____1286 :: uu____1287 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1283 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1272 uu____1282 in
                                       uu____1271
                                         FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1296 =
                                       let uu____1303 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1304 =
                                         let uu____1307 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1307] in
                                       uu____1303 :: uu____1304 in
                                     let uu____1308 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1296
                                       uu____1308 in
                                   let uu____1311 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1311 with
                                   | (expected_k1,uu____1325,uu____1326) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1330 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1330 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1351 ->
                                                 FStar_Exn.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1376 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1376 with
                                     | (act_typ,uu____1384,g_t) ->
                                         let env' =
                                           let uu___362_1387 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___362_1387.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___362_1387.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___362_1387.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___362_1387.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___362_1387.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___362_1387.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___362_1387.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___362_1387.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___362_1387.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___362_1387.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___362_1387.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.failhard =
                                               (uu___362_1387.FStar_TypeChecker_Env.failhard);
                                             FStar_TypeChecker_Env.nosynth =
                                               (uu___362_1387.FStar_TypeChecker_Env.nosynth);
                                             FStar_TypeChecker_Env.tc_term =
                                               (uu___362_1387.FStar_TypeChecker_Env.tc_term);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___362_1387.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___362_1387.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___362_1387.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.is_native_tactic);
                                             FStar_TypeChecker_Env.identifier_info
                                               =
                                               (uu___362_1387.FStar_TypeChecker_Env.identifier_info);
                                             FStar_TypeChecker_Env.tc_hooks =
                                               (uu___362_1387.FStar_TypeChecker_Env.tc_hooks);
                                             FStar_TypeChecker_Env.dsenv =
                                               (uu___362_1387.FStar_TypeChecker_Env.dsenv)
                                           } in
                                         ((let uu____1389 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1389
                                           then
                                             let uu____1390 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1391 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1390 uu____1391
                                           else ());
                                          (let uu____1393 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1393 with
                                           | (act_defn,uu____1401,g_a) ->
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
                                               let uu____1405 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1433 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1433 with
                                                      | (bs1,uu____1443) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1450 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1450 in
                                                          let uu____1453 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1453
                                                           with
                                                           | (k1,uu____1465,g)
                                                               -> (k1, g)))
                                                 | uu____1467 ->
                                                     let uu____1468 =
                                                       let uu____1469 =
                                                         let uu____1474 =
                                                           let uu____1475 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1476 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1475
                                                             uu____1476 in
                                                         (uu____1474,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1469 in
                                                     FStar_Exn.raise
                                                       uu____1468 in
                                               (match uu____1405 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1485 =
                                                        let uu____1486 =
                                                          let uu____1487 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1487 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1486 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1485);
                                                     (let act_typ2 =
                                                        let uu____1491 =
                                                          let uu____1492 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1492.FStar_Syntax_Syntax.n in
                                                        match uu____1491 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1515 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1515
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1524
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1524
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1546
                                                                    =
                                                                    let uu____1547
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1547] in
                                                                    let uu____1548
                                                                    =
                                                                    let uu____1557
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1557] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1546;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1548;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1558
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1558))
                                                        | uu____1561 ->
                                                            failwith
                                                              "Impossible (expected_k is an arrow)" in
                                                      let uu____1564 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1564 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let act_typ4 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              univs1 act_typ3 in
                                                          let uu___363_1573 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___363_1573.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___363_1573.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___363_1573.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ4
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____921 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1597 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1597 in
                               let uu____1600 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1600 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1608 =
                                        let uu____1613 =
                                          let uu____1614 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1614.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1613) in
                                      match uu____1608 with
                                      | ([],uu____1617) -> t1
                                      | (uu____1628,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1629,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1647 ->
                                          failwith
                                            "Impossible : t is an arrow" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1660 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1660 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1665 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1667 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1667))
                                           && (m <> n1) in
                                       if uu____1665
                                       then
                                         let error1 =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let err_msg =
                                           let uu____1683 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1684 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error1 uu____1683 uu____1684 in
                                         FStar_Exn.raise
                                           (FStar_Errors.Error
                                              (err_msg,
                                                ((FStar_Pervasives_Native.snd
                                                    ts1).FStar_Syntax_Syntax.pos)))
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1692 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1692 with
                                      | (univs2,defn) ->
                                          let uu____1699 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1699 with
                                           | (univs',typ) ->
                                               let uu___364_1709 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___364_1709.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___364_1709.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___364_1709.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___365_1714 = ed2 in
                                      let uu____1715 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1716 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1717 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1718 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1719 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1720 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1721 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1722 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1723 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1724 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1725 =
                                        let uu____1726 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1726 in
                                      let uu____1737 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1738 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1739 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___365_1714.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___365_1714.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1715;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1716;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1717;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1718;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1719;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1720;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1721;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1722;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1723;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1724;
                                        FStar_Syntax_Syntax.repr = uu____1725;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1737;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1738;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1739
                                      } in
                                    ((let uu____1743 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1743
                                      then
                                        let uu____1744 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1744
                                      else ());
                                     ed3)))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____1762 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1762 with
      | (effect_binders_un,signature_un) ->
          let uu____1779 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1779 with
           | (effect_binders,env1,uu____1798) ->
               let uu____1799 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1799 with
                | (signature,uu____1815) ->
                    let raise_error err_msg =
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           (err_msg, (signature.FStar_Syntax_Syntax.pos))) in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1843  ->
                           match uu____1843 with
                           | (bv,qual) ->
                               let uu____1854 =
                                 let uu___366_1855 = bv in
                                 let uu____1856 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___366_1855.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___366_1855.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1856
                                 } in
                               (uu____1854, qual)) effect_binders in
                    let uu____1859 =
                      let uu____1866 =
                        let uu____1867 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1867.FStar_Syntax_Syntax.n in
                      match uu____1866 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1877)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1899 ->
                          raise_error
                            "bad shape for effect-for-free signature" in
                    (match uu____1859 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1923 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1923
                           then
                             let uu____1924 =
                               let uu____1927 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1927 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1924
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1961 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1961 with
                           | (t2,comp,uu____1974) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1981 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1981 with
                          | (repr,_comp) ->
                              ((let uu____2003 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2003
                                then
                                  let uu____2004 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2004
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
                                  let uu____2010 =
                                    let uu____2011 =
                                      let uu____2012 =
                                        let uu____2027 =
                                          let uu____2034 =
                                            let uu____2039 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2040 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2039, uu____2040) in
                                          [uu____2034] in
                                        (wp_type1, uu____2027) in
                                      FStar_Syntax_Syntax.Tm_app uu____2012 in
                                    mk1 uu____2011 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2010 in
                                let effect_signature =
                                  let binders =
                                    let uu____2065 =
                                      let uu____2070 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2070) in
                                    let uu____2071 =
                                      let uu____2078 =
                                        let uu____2079 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2079
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2078] in
                                    uu____2065 :: uu____2071 in
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
                                  let uu____2142 = item in
                                  match uu____2142 with
                                  | (u_item,item1) ->
                                      let uu____2163 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2163 with
                                       | (item2,item_comp) ->
                                           ((let uu____2179 =
                                               let uu____2180 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2180 in
                                             if uu____2179
                                             then
                                               let uu____2181 =
                                                 let uu____2182 =
                                                   let uu____2183 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2184 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2183 uu____2184 in
                                                 FStar_Errors.Err uu____2182 in
                                               FStar_Exn.raise uu____2181
                                             else ());
                                            (let uu____2186 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2186 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2206 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2206 with
                                | (dmff_env1,uu____2230,bind_wp,bind_elab) ->
                                    let uu____2233 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2233 with
                                     | (dmff_env2,uu____2257,return_wp,return_elab)
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
                                           let uu____2264 =
                                             let uu____2265 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2265.FStar_Syntax_Syntax.n in
                                           match uu____2264 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2309 =
                                                 let uu____2324 =
                                                   let uu____2329 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2329 in
                                                 match uu____2324 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2393 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2309 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2432 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2432 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2449 =
                                                          let uu____2450 =
                                                            let uu____2465 =
                                                              let uu____2472
                                                                =
                                                                let uu____2477
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2478
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2477,
                                                                  uu____2478) in
                                                              [uu____2472] in
                                                            (wp_type1,
                                                              uu____2465) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2450 in
                                                        mk1 uu____2449 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2493 =
                                                      let uu____2502 =
                                                        let uu____2503 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2503 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2502 in
                                                    (match uu____2493 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2522
                                                           =
                                                           let error_msg =
                                                             let uu____2524 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2524
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
                                                                (let uu____2530
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
                                                                   uu____2530
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
                                                             let uu____2557 =
                                                               let uu____2558
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2559
                                                                 =
                                                                 let uu____2560
                                                                   =
                                                                   let uu____2567
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2567,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2560] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2558
                                                                 uu____2559 in
                                                             uu____2557
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2592 =
                                                             let uu____2593 =
                                                               let uu____2600
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2600] in
                                                             b11 ::
                                                               uu____2593 in
                                                           let uu____2605 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2592
                                                             uu____2605
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2606 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2608 =
                                             let uu____2609 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2609.FStar_Syntax_Syntax.n in
                                           match uu____2608 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2653 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2653
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2666 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2668 =
                                             let uu____2669 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2669.FStar_Syntax_Syntax.n in
                                           match uu____2668 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2696 =
                                                 let uu____2697 =
                                                   let uu____2700 =
                                                     let uu____2701 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2701 in
                                                   [uu____2700] in
                                                 FStar_List.append uu____2697
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2696 body what
                                           | uu____2702 ->
                                               raise_error
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2720 =
                                                let uu____2721 =
                                                  let uu____2722 =
                                                    let uu____2737 =
                                                      let uu____2738 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2738 in
                                                    (t, uu____2737) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2722 in
                                                mk1 uu____2721 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2720) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2768 = f a2 in
                                               [uu____2768]
                                           | x::xs ->
                                               let uu____2773 =
                                                 apply_last1 f xs in
                                               x :: uu____2773 in
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
                                           let uu____2793 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2793 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2823 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2823
                                                 then
                                                   let uu____2824 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2824
                                                 else ());
                                                (let uu____2826 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2826))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2835 =
                                                 let uu____2840 = mk_lid name in
                                                 let uu____2841 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2840 uu____2841 in
                                               (match uu____2835 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2845 =
                                                        let uu____2848 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____2848 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____2845);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____2983 =
                                             let uu____2986 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2987 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____2986 :: uu____2987 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____2983);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3123 =
                                               let uu____3126 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3127 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3126 :: uu____3127 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3123);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3260 =
                                                FStar_List.fold_left
                                                  (fun uu____3300  ->
                                                     fun action  ->
                                                       match uu____3300 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3321 =
                                                             let uu____3328 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3328
                                                               params_un in
                                                           (match uu____3321
                                                            with
                                                            | (action_params,env',uu____3337)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3357
                                                                     ->
                                                                    match uu____3357
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3368
                                                                    =
                                                                    let uu___367_3369
                                                                    = bv in
                                                                    let uu____3370
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___367_3369.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___367_3369.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3370
                                                                    } in
                                                                    (uu____3368,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3374
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3374
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
                                                                    uu____3404
                                                                    ->
                                                                    let uu____3405
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3405 in
                                                                    ((
                                                                    let uu____3409
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3409
                                                                    then
                                                                    let uu____3410
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3411
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3412
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3413
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3410
                                                                    uu____3411
                                                                    uu____3412
                                                                    uu____3413
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
                                                                    let uu____3417
                                                                    =
                                                                    let uu____3420
                                                                    =
                                                                    let uu___368_3421
                                                                    = action in
                                                                    let uu____3422
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3423
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___368_3421.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___368_3421.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___368_3421.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3422;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3423
                                                                    } in
                                                                    uu____3420
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3417))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3260 with
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
                                                      let uu____3456 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3457 =
                                                        let uu____3460 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3460] in
                                                      uu____3456 ::
                                                        uu____3457 in
                                                    let uu____3461 =
                                                      let uu____3462 =
                                                        let uu____3463 =
                                                          let uu____3464 =
                                                            let uu____3479 =
                                                              let uu____3486
                                                                =
                                                                let uu____3491
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3492
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3491,
                                                                  uu____3492) in
                                                              [uu____3486] in
                                                            (repr,
                                                              uu____3479) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3464 in
                                                        mk1 uu____3463 in
                                                      let uu____3507 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3462
                                                        uu____3507 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3461
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3510 =
                                                    let uu____3517 =
                                                      let uu____3518 =
                                                        let uu____3521 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3521 in
                                                      uu____3518.FStar_Syntax_Syntax.n in
                                                    match uu____3517 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3531)
                                                        ->
                                                        let uu____3560 =
                                                          let uu____3577 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3577
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3635 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3560
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3685 =
                                                               let uu____3686
                                                                 =
                                                                 let uu____3689
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3689 in
                                                               uu____3686.FStar_Syntax_Syntax.n in
                                                             (match uu____3685
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3714
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3714
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3727
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3752
                                                                     ->
                                                                    match uu____3752
                                                                    with
                                                                    | 
                                                                    (bv,uu____3758)
                                                                    ->
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3760
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3760
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3759
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3727
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
                                                                    let uu____3824
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3824 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg)
                                                                    | 
                                                                    uu____3829
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3837
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3837 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg) in
                                                                    let uu____3842
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3845
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3842,
                                                                    uu____3845)))
                                                              | uu____3852 ->
                                                                  let uu____3853
                                                                    =
                                                                    let uu____3854
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3854 in
                                                                  raise_error
                                                                    uu____3853))
                                                    | uu____3861 ->
                                                        let uu____3862 =
                                                          let uu____3863 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3863 in
                                                        raise_error
                                                          uu____3862 in
                                                  (match uu____3510 with
                                                   | (pre,post) ->
                                                       ((let uu____3887 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3889 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3891 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___369_3893
                                                             = ed in
                                                           let uu____3894 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3895 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3896 =
                                                             let uu____3897 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3897) in
                                                           let uu____3904 =
                                                             let uu____3905 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3905) in
                                                           let uu____3912 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3913 =
                                                             let uu____3914 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3914) in
                                                           let uu____3921 =
                                                             let uu____3922 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3922) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3894;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3895;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3896;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3904;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___369_3893.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3912;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3913;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3921;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3929 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3929
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3947
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3947
                                                               then
                                                                 let uu____3948
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3948
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
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3972
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____3972) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3963 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3960;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____3987
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3987
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____3989
                                                                 =
                                                                 let uu____3992
                                                                   =
                                                                   let uu____3995
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____3995 in
                                                                 FStar_List.append
                                                                   uu____3992
                                                                   sigelts' in
                                                               (uu____3989,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4071 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4071 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4104 = FStar_List.hd ses in
            uu____4104.FStar_Syntax_Syntax.sigrng in
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
           | uu____4109 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Invalid (partial) redefinition of lex_t", err_range)));
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4114,uu____4115);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4117;
               FStar_Syntax_Syntax.sigattrs = uu____4118;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4122);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4124;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4125;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4129);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4131;
                 FStar_Syntax_Syntax.sigattrs = uu____4132;_}::[]
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
                 let uu____4197 =
                   let uu____4200 =
                     let uu____4201 =
                       let uu____4208 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4208, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4201 in
                   FStar_Syntax_Syntax.mk uu____4200 in
                 uu____4197 FStar_Pervasives_Native.None r1 in
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
                   let uu____4226 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4226 in
                 let hd1 =
                   let uu____4228 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4228 in
                 let tl1 =
                   let uu____4230 =
                     let uu____4231 =
                       let uu____4234 =
                         let uu____4235 =
                           let uu____4242 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4242, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4235 in
                       FStar_Syntax_Syntax.mk uu____4234 in
                     uu____4231 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4230 in
                 let res =
                   let uu____4251 =
                     let uu____4254 =
                       let uu____4255 =
                         let uu____4262 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4262,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4255 in
                     FStar_Syntax_Syntax.mk uu____4254 in
                   uu____4251 FStar_Pervasives_Native.None r2 in
                 let uu____4268 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4268 in
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
               let uu____4307 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4307;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4312 ->
               let err_msg =
                 let uu____4316 =
                   let uu____4317 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4317 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4316 in
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
            let uu____4342 = FStar_Syntax_Util.type_u () in
            match uu____4342 with
            | (k,uu____4348) ->
                let phi1 =
                  let uu____4350 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4350
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4352 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4352 with
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
          let uu____4394 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4394 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4427 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4427 FStar_List.flatten in
              ((let uu____4441 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4441
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
                          let uu____4452 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4462,uu____4463,uu____4464,uu____4465,uu____4466)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4475 -> failwith "Impossible!" in
                          match uu____4452 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4486 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4490,uu____4491,uu____4492,uu____4493,uu____4494)
                        -> lid
                    | uu____4503 -> failwith "Impossible" in
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
                  let uu____4521 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4521
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
                     let uu____4544 =
                       let uu____4547 =
                         let uu____4548 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4548;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4547 :: ses1 in
                     (uu____4544, data_ops_ses)) in
                (let uu____4558 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4592 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4617 ->
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
           let uu____4669 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4669 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4708 = FStar_Options.set_options t s in
             match uu____4708 with
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
                ((let uu____4734 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4734 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4742 = cps_and_elaborate env1 ne in
           (match uu____4742 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___370_4779 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___370_4779.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___370_4779.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___370_4779.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___370_4779.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___371_4781 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___371_4781.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___371_4781.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___371_4781.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___371_4781.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___372_4789 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___372_4789.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___372_4789.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___372_4789.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___372_4789.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4797 =
             let uu____4804 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4804 in
           (match uu____4797 with
            | (a,wp_a_src) ->
                let uu____4819 =
                  let uu____4826 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4826 in
                (match uu____4819 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4842 =
                         let uu____4845 =
                           let uu____4846 =
                             let uu____4853 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4853) in
                           FStar_Syntax_Syntax.NT uu____4846 in
                         [uu____4845] in
                       FStar_Syntax_Subst.subst uu____4842 wp_b_tgt in
                     let expected_k =
                       let uu____4857 =
                         let uu____4864 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4865 =
                           let uu____4868 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4868] in
                         uu____4864 :: uu____4865 in
                       let uu____4869 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4857 uu____4869 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4890 =
                           let uu____4891 =
                             let uu____4896 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4897 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4896, uu____4897) in
                           FStar_Errors.Error uu____4891 in
                         FStar_Exn.raise uu____4890 in
                       let uu____4900 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4900 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4932 =
                             let uu____4933 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4933 in
                           if uu____4932
                           then no_reify eff_name
                           else
                             (let uu____4939 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4940 =
                                let uu____4943 =
                                  let uu____4944 =
                                    let uu____4959 =
                                      let uu____4962 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____4963 =
                                        let uu____4966 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____4966] in
                                      uu____4962 :: uu____4963 in
                                    (repr, uu____4959) in
                                  FStar_Syntax_Syntax.Tm_app uu____4944 in
                                FStar_Syntax_Syntax.mk uu____4943 in
                              uu____4940 FStar_Pervasives_Native.None
                                uu____4939) in
                     let uu____4972 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5000,lift_wp)) ->
                           let uu____5024 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5024)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5050 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5050
                             then
                               let uu____5051 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5051
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____5054 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5054 with
                             | (lift1,comp,uu____5069) ->
                                 let uu____5070 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5070 with
                                  | (uu____5083,lift_wp,lift_elab) ->
                                      let uu____5086 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5087 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____4972 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___373_5128 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___373_5128.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___373_5128.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___373_5128.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___373_5128.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___373_5128.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___373_5128.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___373_5128.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___373_5128.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___373_5128.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___373_5128.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___373_5128.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___373_5128.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___373_5128.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___373_5128.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___373_5128.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___373_5128.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___373_5128.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___373_5128.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___373_5128.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___373_5128.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___373_5128.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___373_5128.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___373_5128.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___373_5128.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___373_5128.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___373_5128.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___373_5128.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___373_5128.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___373_5128.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___373_5128.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___373_5128.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___373_5128.FStar_TypeChecker_Env.dsenv)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5134,lift1)
                                ->
                                let uu____5146 =
                                  let uu____5153 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5153 in
                                (match uu____5146 with
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
                                         let uu____5177 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5178 =
                                           let uu____5181 =
                                             let uu____5182 =
                                               let uu____5197 =
                                                 let uu____5200 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5201 =
                                                   let uu____5204 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5204] in
                                                 uu____5200 :: uu____5201 in
                                               (lift_wp1, uu____5197) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5182 in
                                           FStar_Syntax_Syntax.mk uu____5181 in
                                         uu____5178
                                           FStar_Pervasives_Native.None
                                           uu____5177 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5213 =
                                         let uu____5220 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5221 =
                                           let uu____5224 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5225 =
                                             let uu____5228 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5228] in
                                           uu____5224 :: uu____5225 in
                                         uu____5220 :: uu____5221 in
                                       let uu____5229 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5213
                                         uu____5229 in
                                     let uu____5232 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5232 with
                                      | (expected_k2,uu____5242,uu____5243)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___374_5246 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___374_5246.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___374_5246.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___375_5248 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___375_5248.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___375_5248.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___375_5248.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___375_5248.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5267 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5267 with
            | (tps1,c1) ->
                let uu____5282 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5282 with
                 | (tps2,env3,us) ->
                     let uu____5300 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5300 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5321 =
                              let uu____5322 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5322 in
                            match uu____5321 with
                            | (uvs1,t) ->
                                let uu____5337 =
                                  let uu____5350 =
                                    let uu____5355 =
                                      let uu____5356 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5356.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5355) in
                                  match uu____5350 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5371,c4)) -> ([], c4)
                                  | (uu____5411,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5438 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5337 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5482 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5482 with
                                         | (uu____5487,t1) ->
                                             let uu____5489 =
                                               let uu____5490 =
                                                 let uu____5495 =
                                                   let uu____5496 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5497 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5498 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5496 uu____5497
                                                     uu____5498 in
                                                 (uu____5495, r) in
                                               FStar_Errors.Error uu____5490 in
                                             FStar_Exn.raise uu____5489)
                                      else ();
                                      (let se1 =
                                         let uu___376_5501 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___376_5501.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___376_5501.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___376_5501.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___376_5501.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5518,uu____5519,uu____5520) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___351_5524  ->
                   match uu___351_5524 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5525 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5530,uu____5531) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___351_5539  ->
                   match uu___351_5539 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5540 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5550 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5550
             then
               let uu____5551 =
                 let uu____5552 =
                   let uu____5557 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5557, r) in
                 FStar_Errors.Error uu____5552 in
               FStar_Exn.raise uu____5551
             else ());
            (let uu____5559 =
               if uvs = []
               then
                 let uu____5560 =
                   let uu____5561 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5561 in
                 check_and_gen env2 t uu____5560
               else
                 (let uu____5567 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5567 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5575 =
                          let uu____5576 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5576 in
                        tc_check_trivial_guard env2 t1 uu____5575 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5582 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5582)) in
             match uu____5559 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___377_5598 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___377_5598.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___377_5598.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___377_5598.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___377_5598.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5608 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5608 with
            | (uu____5621,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5631 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5631 with
            | (e1,c,g1) ->
                let uu____5649 =
                  let uu____5656 =
                    let uu____5659 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5659 in
                  let uu____5660 =
                    let uu____5665 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5665) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5656 uu____5660 in
                (match uu____5649 with
                 | (e2,uu____5679,g) ->
                     ((let uu____5682 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5682);
                      (let se1 =
                         let uu___378_5684 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___378_5684.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___378_5684.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___378_5684.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___378_5684.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5735 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5735
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5743 =
                      let uu____5744 =
                        let uu____5749 =
                          let uu____5750 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5751 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5752 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5750 uu____5751 uu____5752 in
                        (uu____5749, r) in
                      FStar_Errors.Error uu____5744 in
                    FStar_Exn.raise uu____5743) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5778 =
                   let uu____5779 = FStar_Syntax_Subst.compress def in
                   uu____5779.FStar_Syntax_Syntax.n in
                 match uu____5778 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5789,uu____5790)
                     -> binders
                 | uu____5811 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5821;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5899) -> val_bs1
                     | (uu____5922,[]) -> val_bs1
                     | ((body_bv,uu____5946)::bt,(val_bv,aqual)::vt) ->
                         let uu____5983 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____5999) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___379_6001 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___380_6004 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___380_6004.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___379_6001.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___379_6001.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____5983 in
                   let uu____6005 =
                     let uu____6008 =
                       let uu____6009 =
                         let uu____6022 = rename_binders1 def_bs val_bs in
                         (uu____6022, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6009 in
                     FStar_Syntax_Syntax.mk uu____6008 in
                   uu____6005 FStar_Pervasives_Native.None r1
               | uu____6040 -> typ1 in
             let uu___381_6041 = lb in
             let uu____6042 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___381_6041.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___381_6041.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6042;
               FStar_Syntax_Syntax.lbeff =
                 (uu___381_6041.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___381_6041.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____6045 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6096  ->
                     fun lb  ->
                       match uu____6096 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6138 =
                             let uu____6149 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6149 with
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
                                   | uu____6234 ->
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
                                  (let uu____6277 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6277, quals_opt1))) in
                           (match uu____6138 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6045 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6371 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___352_6375  ->
                                match uu___352_6375 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6376 -> false)) in
                      if uu____6371
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6386 =
                    let uu____6389 =
                      let uu____6390 =
                        let uu____6403 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6403) in
                      FStar_Syntax_Syntax.Tm_let uu____6390 in
                    FStar_Syntax_Syntax.mk uu____6389 in
                  uu____6386 FStar_Pervasives_Native.None r in
                let uu____6421 =
                  let uu____6432 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___382_6441 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___382_6441.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___382_6441.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___382_6441.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___382_6441.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___382_6441.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___382_6441.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___382_6441.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___382_6441.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___382_6441.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___382_6441.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___382_6441.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___382_6441.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___382_6441.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___382_6441.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___382_6441.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___382_6441.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___382_6441.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___382_6441.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___382_6441.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___382_6441.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___382_6441.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___382_6441.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___382_6441.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___382_6441.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___382_6441.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___382_6441.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___382_6441.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___382_6441.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___382_6441.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___382_6441.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___382_6441.FStar_TypeChecker_Env.dsenv)
                       }) e in
                  match uu____6432 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6454;
                       FStar_Syntax_Syntax.vars = uu____6455;_},uu____6456,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6485 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6485) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6503,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6508 -> quals in
                      ((let uu___383_6516 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___383_6516.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___383_6516.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___383_6516.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6525 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6421 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6574 = log env2 in
                       if uu____6574
                       then
                         let uu____6575 =
                           let uu____6576 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6591 =
                                         let uu____6600 =
                                           let uu____6601 =
                                             let uu____6604 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6604.FStar_Syntax_Syntax.fv_name in
                                           uu____6601.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6600 in
                                       match uu____6591 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6611 -> false in
                                     if should_log
                                     then
                                       let uu____6620 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6621 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6620 uu____6621
                                     else "")) in
                           FStar_All.pipe_right uu____6576
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6575
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6652 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6652 with
                              | (bs1,c1) ->
                                  let uu____6659 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6659
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6671 =
                                            let uu____6672 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6672.FStar_Syntax_Syntax.n in
                                          (match uu____6671 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6697 =
                                                 let uu____6698 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6698.FStar_Syntax_Syntax.n in
                                               (match uu____6697 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6708 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6708 in
                                                    let uu____6709 =
                                                      let uu____6710 =
                                                        let uu____6711 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6711 args in
                                                      uu____6710
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6709 u
                                                | uu____6714 -> c1)
                                           | uu____6715 -> c1)
                                      | uu____6716 -> c1 in
                                    let uu___384_6717 = t1 in
                                    let uu____6718 =
                                      let uu____6719 =
                                        let uu____6732 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6732) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6719 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6718;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___384_6717.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___384_6717.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6756 =
                               let uu____6757 = FStar_Syntax_Subst.compress h in
                               uu____6757.FStar_Syntax_Syntax.n in
                             (match uu____6756 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6767 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6767 in
                                  let uu____6768 =
                                    let uu____6769 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6769
                                      args in
                                  uu____6768 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6772 -> t1)
                         | uu____6773 -> t1 in
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
                           let uu____6801 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6801 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6818 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6818, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6849 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6849 in
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
                         let uu___385_6856 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___386_6868 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___386_6868.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___386_6868.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___386_6868.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___386_6868.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___385_6856.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___385_6856.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___385_6856.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___385_6856.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6885 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6885 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6919 =
                                    let uu____6920 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6920.FStar_Syntax_Syntax.n in
                                  (match uu____6919 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6953 =
                                           let uu____6956 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6956.FStar_Syntax_Syntax.fv_name in
                                         uu____6953.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6958 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6958 in
                                       let uu____6959 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____6959 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____6969 =
                                              let uu____6970 =
                                                let uu____6971 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____6971 in
                                              Prims.op_Negation uu____6970 in
                                            if uu____6969
                                            then
                                              ((let uu____7001 =
                                                  let uu____7002 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____7002 in
                                                if uu____7001
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
                                               (let uu____7109 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid in
                                                if uu____7109
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
                                   | uu____7138 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7143 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7165 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7165
                             then
                               let uu____7166 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7167 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7166 uu____7167
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
             (fun uu___353_7218  ->
                match uu___353_7218 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7219 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7225) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7231 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7240 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7245 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7270 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7294) ->
          let uu____7303 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7303
          then
            let for_export_bundle se1 uu____7334 =
              match uu____7334 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7373,uu____7374) ->
                       let dec =
                         let uu___387_7384 = se1 in
                         let uu____7385 =
                           let uu____7386 =
                             let uu____7393 =
                               let uu____7396 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7396 in
                             (l, us, uu____7393) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7386 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7385;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___387_7384.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___387_7384.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___387_7384.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7408,uu____7409,uu____7410) ->
                       let dec =
                         let uu___388_7416 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___388_7416.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___388_7416.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___388_7416.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7421 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7443,uu____7444,uu____7445) ->
          let uu____7446 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7446 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7467 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7467
          then
            ([(let uu___389_7483 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___389_7483.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___389_7483.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___389_7483.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7485 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___354_7489  ->
                       match uu___354_7489 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7490 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7495 -> true
                       | uu____7496 -> false)) in
             if uu____7485 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7514 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7519 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7524 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7529 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7534 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7552) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7569 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7569
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
          let uu____7600 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7600
          then
            let uu____7609 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___390_7622 = se in
                      let uu____7623 =
                        let uu____7624 =
                          let uu____7631 =
                            let uu____7632 =
                              let uu____7635 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7635.FStar_Syntax_Syntax.fv_name in
                            uu____7632.FStar_Syntax_Syntax.v in
                          (uu____7631, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7624 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7623;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___390_7622.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___390_7622.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___390_7622.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7609, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7655 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7672 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7687) ->
          let env1 =
            let uu____7691 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7691 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7693 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7694 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7704 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7704) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7705,uu____7706,uu____7707) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___355_7711  ->
                  match uu___355_7711 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7712 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7713,uu____7714) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___355_7722  ->
                  match uu___355_7722 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7723 -> false))
          -> env
      | uu____7724 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7784 se =
        match uu____7784 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7837 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7837
              then
                let uu____7838 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7838
              else ());
             (let uu____7840 = tc_decl env1 se in
              match uu____7840 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7890 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7890
                             then
                               let uu____7891 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7891
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
                    (let uu____7914 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7914
                     then
                       let uu____7915 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7921 =
                                  let uu____7922 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7922 "\n" in
                                Prims.strcat s uu____7921) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7915
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7927 =
                       let accum_exports_hidden uu____7957 se1 =
                         match uu____7957 with
                         | (exports1,hidden1) ->
                             let uu____7985 = for_export hidden1 se1 in
                             (match uu____7985 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7927 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___391_8064 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___391_8064.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___391_8064.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___391_8064.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___391_8064.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8142 = acc in
        match uu____8142 with
        | (uu____8177,uu____8178,env1,uu____8180) ->
            let uu____8193 =
              FStar_Util.record_time
                (fun uu____8239  -> process_one_decl acc se) in
            (match uu____8193 with
             | (r,ms_elapsed) ->
                 ((let uu____8303 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8303
                   then
                     let uu____8304 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8305 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8304 uu____8305
                   else ());
                  r)) in
      let uu____8307 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8307 with
      | (ses1,exports,env1,uu____8355) ->
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
        (let uu____8395 = FStar_Options.debug_any () in
         if uu____8395
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
           let uu___392_8401 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___392_8401.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___392_8401.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___392_8401.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___392_8401.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___392_8401.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___392_8401.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___392_8401.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___392_8401.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___392_8401.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___392_8401.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___392_8401.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___392_8401.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___392_8401.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___392_8401.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___392_8401.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___392_8401.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___392_8401.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___392_8401.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___392_8401.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___392_8401.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___392_8401.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___392_8401.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___392_8401.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___392_8401.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___392_8401.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___392_8401.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___392_8401.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___392_8401.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___392_8401.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___392_8401.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___392_8401.FStar_TypeChecker_Env.dsenv)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8405 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8405 with
          | (ses,exports,env3) ->
              ((let uu___393_8438 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___393_8438.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___393_8438.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___393_8438.FStar_Syntax_Syntax.is_interface)
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
        let uu____8460 = tc_decls env decls in
        match uu____8460 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___394_8491 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___394_8491.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___394_8491.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___394_8491.FStar_Syntax_Syntax.is_interface)
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
          let uu___395_8508 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___395_8508.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___395_8508.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___395_8508.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___395_8508.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___395_8508.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___395_8508.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___395_8508.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___395_8508.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___395_8508.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___395_8508.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___395_8508.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___395_8508.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___395_8508.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___395_8508.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___395_8508.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___395_8508.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___395_8508.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___395_8508.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___395_8508.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___395_8508.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___395_8508.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___395_8508.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___395_8508.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___395_8508.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___395_8508.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___395_8508.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___395_8508.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___395_8508.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___395_8508.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___395_8508.FStar_TypeChecker_Env.dsenv)
          } in
        let check_term1 lid univs1 t =
          let uu____8519 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8519 with
          | (univs2,t1) ->
              ((let uu____8527 =
                  let uu____8528 =
                    let uu____8531 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8531 in
                  FStar_All.pipe_left uu____8528
                    (FStar_Options.Other "Exports") in
                if uu____8527
                then
                  let uu____8532 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8533 =
                    let uu____8534 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8534
                      (FStar_String.concat ", ") in
                  let uu____8543 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8532 uu____8533 uu____8543
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8546 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8546 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8570 =
             let uu____8571 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8572 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8571 uu____8572 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8570);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8579) ->
              let uu____8588 =
                let uu____8589 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8589 in
              if uu____8588
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8599,uu____8600) ->
              let t =
                let uu____8612 =
                  let uu____8615 =
                    let uu____8616 =
                      let uu____8629 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8629) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8616 in
                  FStar_Syntax_Syntax.mk uu____8615 in
                uu____8612 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8636,uu____8637,uu____8638) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8646 =
                let uu____8647 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8647 in
              if uu____8646 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8651,lbs),uu____8653) ->
              let uu____8668 =
                let uu____8669 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8669 in
              if uu____8668
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
              let uu____8688 =
                let uu____8689 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8689 in
              if uu____8688
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8696 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8697 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8704 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8705 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8706 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8707 -> () in
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
      (let uu____8721 =
         let uu____8722 = FStar_Options.interactive () in
         Prims.op_Negation uu____8722 in
       if uu____8721
       then
         let uu____8723 = FStar_Options.restore_cmd_line_options true in
         FStar_All.pipe_right uu____8723 FStar_Pervasives.ignore
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
          let uu___396_8739 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___396_8739.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___396_8739.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8742 =
           let uu____8743 = FStar_Options.lax () in
           Prims.op_Negation uu____8743 in
         if uu____8742 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8749 =
           let uu____8750 = FStar_Options.interactive () in
           Prims.op_Negation uu____8750 in
         if uu____8749
         then
           let uu____8751 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8751 FStar_Pervasives.ignore
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
      let uu____8763 = tc_partial_modul env modul true in
      match uu____8763 with
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
      (let uu____8794 = FStar_Options.debug_any () in
       if uu____8794
       then
         let uu____8795 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8795
       else ());
      (let env1 =
         let uu___397_8799 = env in
         let uu____8800 =
           let uu____8801 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8801 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___397_8799.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___397_8799.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___397_8799.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___397_8799.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___397_8799.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___397_8799.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___397_8799.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___397_8799.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___397_8799.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___397_8799.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___397_8799.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___397_8799.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___397_8799.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___397_8799.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___397_8799.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___397_8799.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___397_8799.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___397_8799.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8800;
           FStar_TypeChecker_Env.lax_universes =
             (uu___397_8799.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___397_8799.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___397_8799.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___397_8799.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___397_8799.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___397_8799.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___397_8799.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___397_8799.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___397_8799.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___397_8799.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___397_8799.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___397_8799.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___397_8799.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___397_8799.FStar_TypeChecker_Env.dsenv)
         } in
       let uu____8802 = tc_modul env1 m in
       match uu____8802 with
       | (m1,env2) ->
           ((let uu____8814 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8814
             then
               let uu____8815 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8815
             else ());
            (let uu____8818 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8818
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
                       let uu____8849 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8849 with
                       | (univnames1,e) ->
                           let uu___398_8856 = lb in
                           let uu____8857 =
                             let uu____8860 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8860 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___398_8856.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___398_8856.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___398_8856.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___398_8856.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8857
                           } in
                     let uu___399_8861 = se in
                     let uu____8862 =
                       let uu____8863 =
                         let uu____8870 =
                           let uu____8877 = FStar_List.map update lbs in
                           (b, uu____8877) in
                         (uu____8870, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8863 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8862;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___399_8861.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___399_8861.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___399_8861.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___399_8861.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8890 -> se in
               let normalized_module =
                 let uu___400_8892 = m1 in
                 let uu____8893 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___400_8892.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8893;
                   FStar_Syntax_Syntax.exports =
                     (uu___400_8892.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___400_8892.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8894 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8894
             else ());
            (m1, env2)))