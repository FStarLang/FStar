open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____9 = FStar_Options.reuse_hint_for () in
      match uu____9 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____14 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____14 l in
          let uu___119_15 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___119_15.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___119_15.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___119_15.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___119_15.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___119_15.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___119_15.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___119_15.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___119_15.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___119_15.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___119_15.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___119_15.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___119_15.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___119_15.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___119_15.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___119_15.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___119_15.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___119_15.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___119_15.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___119_15.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___119_15.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___119_15.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___119_15.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___119_15.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___119_15.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___119_15.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___119_15.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___119_15.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___119_15.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___119_15.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___119_15.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___119_15.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___119_15.FStar_TypeChecker_Env.dsenv)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____24 = FStar_TypeChecker_Env.current_module env in
                let uu____25 =
                  let uu____26 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____26 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____24 uu____25
            | l::uu____28 -> l in
          let uu___120_31 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___120_31.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___120_31.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___120_31.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___120_31.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___120_31.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___120_31.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___120_31.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___120_31.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___120_31.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___120_31.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___120_31.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___120_31.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___120_31.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___120_31.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___120_31.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___120_31.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___120_31.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___120_31.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___120_31.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___120_31.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___120_31.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___120_31.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___120_31.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___120_31.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___120_31.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___120_31.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___120_31.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___120_31.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___120_31.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___120_31.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___120_31.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___120_31.FStar_TypeChecker_Env.dsenv)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____41 =
         let uu____42 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____42 in
       Prims.op_Negation uu____41)
let get_tactic_fv:
  'Auu____51 .
    'Auu____51 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____67) ->
            let uu____72 =
              let uu____73 = FStar_Syntax_Subst.compress h' in
              uu____73.FStar_Syntax_Syntax.n in
            (match uu____72 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____79 -> FStar_Pervasives_Native.None)
        | uu____80 -> FStar_Pervasives_Native.None
let is_builtin_tactic: FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____88 =
        let uu____91 = FStar_List.splitAt (Prims.parse_int "2") path in
        FStar_Pervasives_Native.fst uu____91 in
      match uu____88 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____104 -> false
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
        let uu____144 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____144 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____168 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____168
         then
           let uu____169 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____169
         else ());
        (let uu____171 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____171 with
         | (t',uu____179,uu____180) ->
             ((let uu____182 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____182
               then
                 let uu____183 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____183
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
        let uu____197 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____197
let check_nogen:
  'Auu____206 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____206 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____226 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____226)
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
        let fail uu____256 =
          let uu____257 =
            let uu____258 =
              let uu____263 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____263, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____258 in
          FStar_Exn.raise uu____257 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____303)::(wp,uu____305)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____320 -> fail ())
        | uu____321 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____333 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____333 with
      | (effect_params_un,signature_un,opening) ->
          let uu____343 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____343 with
           | (effect_params,env,uu____352) ->
               let uu____353 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____353 with
                | (signature,uu____359) ->
                    let ed1 =
                      let uu___121_361 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___121_361.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___121_361.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___121_361.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___121_361.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___121_361.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___121_361.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___121_361.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___121_361.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___121_361.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___121_361.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___121_361.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___121_361.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___121_361.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___121_361.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___121_361.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___121_361.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___121_361.FStar_Syntax_Syntax.actions)
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____367 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening
                                (FStar_Pervasives_Native.snd ts) in
                            ([], t1) in
                          let uu___122_398 = ed1 in
                          let uu____399 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____400 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____401 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____402 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____403 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____404 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____405 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____406 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____407 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____408 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____409 =
                            let uu____410 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            FStar_Pervasives_Native.snd uu____410 in
                          let uu____421 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____422 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____423 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___123_431 = a in
                                 let uu____432 =
                                   let uu____433 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   FStar_Pervasives_Native.snd uu____433 in
                                 let uu____444 =
                                   let uu____445 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   FStar_Pervasives_Native.snd uu____445 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___123_431.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___123_431.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___123_431.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___123_431.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____432;
                                   FStar_Syntax_Syntax.action_typ = uu____444
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___122_398.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___122_398.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___122_398.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___122_398.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___122_398.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____399;
                            FStar_Syntax_Syntax.bind_wp = uu____400;
                            FStar_Syntax_Syntax.if_then_else = uu____401;
                            FStar_Syntax_Syntax.ite_wp = uu____402;
                            FStar_Syntax_Syntax.stronger = uu____403;
                            FStar_Syntax_Syntax.close_wp = uu____404;
                            FStar_Syntax_Syntax.assert_p = uu____405;
                            FStar_Syntax_Syntax.assume_p = uu____406;
                            FStar_Syntax_Syntax.null_wp = uu____407;
                            FStar_Syntax_Syntax.trivial = uu____408;
                            FStar_Syntax_Syntax.repr = uu____409;
                            FStar_Syntax_Syntax.return_repr = uu____421;
                            FStar_Syntax_Syntax.bind_repr = uu____422;
                            FStar_Syntax_Syntax.actions = uu____423
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____482 =
                          let uu____483 =
                            let uu____488 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____488, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____483 in
                        FStar_Exn.raise uu____482 in
                      let uu____495 =
                        let uu____496 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____496.FStar_Syntax_Syntax.n in
                      match uu____495 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____531)::(wp,uu____533)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____548 -> fail signature1)
                      | uu____549 -> fail signature1 in
                    let uu____550 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____550 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____572 =
                           let uu____573 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____573 with
                           | (signature1,uu____585) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____587 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____587 in
                         ((let uu____589 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____589
                           then
                             let uu____590 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____591 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____592 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____593 =
                               let uu____594 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____594 in
                             let uu____595 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____590 uu____591 uu____592 uu____593
                               uu____595
                           else ());
                          (let check_and_gen' env2 uu____611 k =
                             match uu____611 with
                             | (uu____619,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____629 =
                                 let uu____636 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____637 =
                                   let uu____640 =
                                     let uu____641 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____641 in
                                   [uu____640] in
                                 uu____636 :: uu____637 in
                               let uu____642 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____629 uu____642 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____646 = fresh_effect_signature () in
                             match uu____646 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____662 =
                                     let uu____669 =
                                       let uu____670 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____670 in
                                     [uu____669] in
                                   let uu____671 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____662
                                     uu____671 in
                                 let expected_k =
                                   let uu____677 =
                                     let uu____684 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_range in
                                     let uu____685 =
                                       let uu____688 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____689 =
                                         let uu____692 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____693 =
                                           let uu____696 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____697 =
                                             let uu____700 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____700] in
                                           uu____696 :: uu____697 in
                                         uu____692 :: uu____693 in
                                       uu____688 :: uu____689 in
                                     uu____684 :: uu____685 in
                                   let uu____701 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____677
                                     uu____701 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
                               let uu____706 =
                                 let uu____707 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____707
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____706 in
                             let expected_k =
                               let uu____719 =
                                 let uu____726 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____727 =
                                   let uu____730 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____731 =
                                     let uu____734 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____735 =
                                       let uu____738 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____738] in
                                     uu____734 :: uu____735 in
                                   uu____730 :: uu____731 in
                                 uu____726 :: uu____727 in
                               let uu____739 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____719 uu____739 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____746 =
                                 let uu____753 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____754 =
                                   let uu____757 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____757] in
                                 uu____753 :: uu____754 in
                               let uu____758 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____746 uu____758 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____762 = FStar_Syntax_Util.type_u () in
                             match uu____762 with
                             | (t,uu____768) ->
                                 let expected_k =
                                   let uu____772 =
                                     let uu____779 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____780 =
                                       let uu____783 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____784 =
                                         let uu____787 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____787] in
                                       uu____783 :: uu____784 in
                                     uu____779 :: uu____780 in
                                   let uu____788 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____772
                                     uu____788 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
                               let uu____793 =
                                 let uu____794 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____794
                                   FStar_Pervasives_Native.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (FStar_Pervasives_Native.Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____793 in
                             let b_wp_a =
                               let uu____806 =
                                 let uu____813 =
                                   let uu____814 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____814 in
                                 [uu____813] in
                               let uu____815 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____806 uu____815 in
                             let expected_k =
                               let uu____821 =
                                 let uu____828 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____829 =
                                   let uu____832 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____833 =
                                     let uu____836 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____836] in
                                   uu____832 :: uu____833 in
                                 uu____828 :: uu____829 in
                               let uu____837 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____821 uu____837 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____844 =
                                 let uu____851 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____852 =
                                   let uu____855 =
                                     let uu____856 =
                                       let uu____857 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____857
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____856 in
                                   let uu____866 =
                                     let uu____869 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____869] in
                                   uu____855 :: uu____866 in
                                 uu____851 :: uu____852 in
                               let uu____870 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____844 uu____870 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____877 =
                                 let uu____884 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____885 =
                                   let uu____888 =
                                     let uu____889 =
                                       let uu____890 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____890
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____889 in
                                   let uu____899 =
                                     let uu____902 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____902] in
                                   uu____888 :: uu____899 in
                                 uu____884 :: uu____885 in
                               let uu____903 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____877 uu____903 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____910 =
                                 let uu____917 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____917] in
                               let uu____918 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____910 uu____918 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____922 = FStar_Syntax_Util.type_u () in
                             match uu____922 with
                             | (t,uu____928) ->
                                 let expected_k =
                                   let uu____932 =
                                     let uu____939 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____940 =
                                       let uu____943 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____943] in
                                     uu____939 :: uu____940 in
                                   let uu____944 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____932
                                     uu____944 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____947 =
                             let uu____958 =
                               let uu____959 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____959.FStar_Syntax_Syntax.n in
                             match uu____958 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____974 ->
                                 let repr =
                                   let uu____976 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____976 with
                                   | (t,uu____982) ->
                                       let expected_k =
                                         let uu____986 =
                                           let uu____993 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____994 =
                                             let uu____997 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____997] in
                                           uu____993 :: uu____994 in
                                         let uu____998 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____986
                                           uu____998 in
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
                                   let uu____1011 =
                                     let uu____1014 =
                                       let uu____1015 =
                                         let uu____1030 =
                                           let uu____1033 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____1034 =
                                             let uu____1037 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____1037] in
                                           uu____1033 :: uu____1034 in
                                         (repr1, uu____1030) in
                                       FStar_Syntax_Syntax.Tm_app uu____1015 in
                                     FStar_Syntax_Syntax.mk uu____1014 in
                                   uu____1011 FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____1052 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____1052 wp in
                                 let destruct_repr t =
                                   let uu____1065 =
                                     let uu____1066 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____1066.FStar_Syntax_Syntax.n in
                                   match uu____1065 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1077,(t1,uu____1079)::(wp,uu____1081)::[])
                                       -> (t1, wp)
                                   | uu____1124 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____1135 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_All.pipe_right uu____1135
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____1136 = fresh_effect_signature () in
                                   match uu____1136 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1152 =
                                           let uu____1159 =
                                             let uu____1160 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1160 in
                                           [uu____1159] in
                                         let uu____1161 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____1152
                                           uu____1161 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           FStar_Pervasives_Native.None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           FStar_Pervasives_Native.None
                                           a_wp_b in
                                       let x_a =
                                         let uu____1167 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           FStar_Pervasives_Native.None
                                           uu____1167 in
                                       let wp_g_x =
                                         let uu____1171 =
                                           let uu____1172 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____1173 =
                                             let uu____1174 =
                                               let uu____1175 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1175 in
                                             [uu____1174] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1172 uu____1173 in
                                         uu____1171
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____1184 =
                                             let uu____1185 =
                                               let uu____1186 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right
                                                 uu____1186
                                                 FStar_Pervasives_Native.snd in
                                             let uu____1195 =
                                               let uu____1196 =
                                                 let uu____1199 =
                                                   let uu____1202 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1203 =
                                                     let uu____1206 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1207 =
                                                       let uu____1210 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1211 =
                                                         let uu____1214 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1214] in
                                                       uu____1210 ::
                                                         uu____1211 in
                                                     uu____1206 :: uu____1207 in
                                                   uu____1202 :: uu____1203 in
                                                 r :: uu____1199 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1196 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1185 uu____1195 in
                                           uu____1184
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1220 =
                                           let uu____1227 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1228 =
                                             let uu____1231 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1232 =
                                               let uu____1235 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1236 =
                                                 let uu____1239 =
                                                   let uu____1240 =
                                                     let uu____1241 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1241 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1240 in
                                                 let uu____1242 =
                                                   let uu____1245 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1246 =
                                                     let uu____1249 =
                                                       let uu____1250 =
                                                         let uu____1251 =
                                                           let uu____1258 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1258] in
                                                         let uu____1259 =
                                                           let uu____1262 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1262 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1251
                                                           uu____1259 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1250 in
                                                     [uu____1249] in
                                                   uu____1245 :: uu____1246 in
                                                 uu____1239 :: uu____1242 in
                                               uu____1235 :: uu____1236 in
                                             uu____1231 :: uu____1232 in
                                           uu____1227 :: uu____1228 in
                                         let uu____1263 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1220
                                           uu____1263 in
                                       let uu____1266 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____1266 with
                                        | (expected_k1,uu____1274,uu____1275)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
                                              let uu___124_1280 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___124_1280.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___124_1280.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___124_1280.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.failhard
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.failhard);
                                                FStar_TypeChecker_Env.nosynth
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.nosynth);
                                                FStar_TypeChecker_Env.tc_term
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.tc_term);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___124_1280.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.is_native_tactic);
                                                FStar_TypeChecker_Env.identifier_info
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.identifier_info);
                                                FStar_TypeChecker_Env.tc_hooks
                                                  =
                                                  (uu___124_1280.FStar_TypeChecker_Env.tc_hooks);
                                                FStar_TypeChecker_Env.dsenv =
                                                  (uu___124_1280.FStar_TypeChecker_Env.dsenv)
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1290 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a"
                                       FStar_Pervasives_Native.None
                                       uu____1290 in
                                   let res =
                                     let wp =
                                       let uu____1297 =
                                         let uu____1298 =
                                           let uu____1299 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1299
                                             FStar_Pervasives_Native.snd in
                                         let uu____1308 =
                                           let uu____1309 =
                                             let uu____1312 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1313 =
                                               let uu____1316 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1316] in
                                             uu____1312 :: uu____1313 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1309 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1298 uu____1308 in
                                       uu____1297
                                         FStar_Pervasives_Native.None
                                         FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1322 =
                                       let uu____1329 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1330 =
                                         let uu____1333 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1333] in
                                       uu____1329 :: uu____1330 in
                                     let uu____1334 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1322
                                       uu____1334 in
                                   let uu____1337 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1337 with
                                   | (expected_k1,uu____1351,uu____1352) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (FStar_Pervasives_Native.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1356 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1356 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1377 ->
                                                 FStar_Exn.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1402 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1402 with
                                     | (act_typ,uu____1410,g_t) ->
                                         let env' =
                                           let uu___125_1413 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___125_1413.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___125_1413.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___125_1413.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___125_1413.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___125_1413.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___125_1413.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___125_1413.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___125_1413.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___125_1413.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___125_1413.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___125_1413.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.failhard =
                                               (uu___125_1413.FStar_TypeChecker_Env.failhard);
                                             FStar_TypeChecker_Env.nosynth =
                                               (uu___125_1413.FStar_TypeChecker_Env.nosynth);
                                             FStar_TypeChecker_Env.tc_term =
                                               (uu___125_1413.FStar_TypeChecker_Env.tc_term);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___125_1413.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___125_1413.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___125_1413.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.is_native_tactic);
                                             FStar_TypeChecker_Env.identifier_info
                                               =
                                               (uu___125_1413.FStar_TypeChecker_Env.identifier_info);
                                             FStar_TypeChecker_Env.tc_hooks =
                                               (uu___125_1413.FStar_TypeChecker_Env.tc_hooks);
                                             FStar_TypeChecker_Env.dsenv =
                                               (uu___125_1413.FStar_TypeChecker_Env.dsenv)
                                           } in
                                         ((let uu____1415 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1415
                                           then
                                             let uu____1416 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1417 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1416 uu____1417
                                           else ());
                                          (let uu____1419 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1419 with
                                           | (act_defn,uu____1427,g_a) ->
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
                                               let uu____1431 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1459 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1459 with
                                                      | (bs1,uu____1469) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1476 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1476 in
                                                          let uu____1479 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1479
                                                           with
                                                           | (k1,uu____1491,g)
                                                               -> (k1, g)))
                                                 | uu____1493 ->
                                                     let uu____1494 =
                                                       let uu____1495 =
                                                         let uu____1500 =
                                                           let uu____1501 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1502 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1501
                                                             uu____1502 in
                                                         (uu____1500,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1495 in
                                                     FStar_Exn.raise
                                                       uu____1494 in
                                               (match uu____1431 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
                                                    ((let uu____1511 =
                                                        let uu____1512 =
                                                          let uu____1513 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1513 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1512 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1511);
                                                     (let act_typ2 =
                                                        let uu____1517 =
                                                          let uu____1518 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1518.FStar_Syntax_Syntax.n in
                                                        match uu____1517 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1541 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1541
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1550
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                 (match uu____1550
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1572
                                                                    =
                                                                    let uu____1573
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1573] in
                                                                    let uu____1574
                                                                    =
                                                                    let uu____1583
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1583] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1572;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1574;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1584
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1584))
                                                        | uu____1587 ->
                                                            failwith
                                                              "Impossible (expected_k is an arrow)" in
                                                      let uu____1590 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1590 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
                                                          let act_typ4 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              univs1 act_typ3 in
                                                          let uu___126_1599 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___126_1599.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___126_1599.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___126_1599.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ4
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____947 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1623 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1623 in
                               let uu____1626 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1626 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1634 =
                                        let uu____1639 =
                                          let uu____1640 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1640.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1639) in
                                      match uu____1634 with
                                      | ([],uu____1643) -> t1
                                      | (uu____1654,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1655,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1673 ->
                                          failwith
                                            "Impossible : t is an arrow" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1686 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1686 in
                                      let m =
                                        FStar_List.length
                                          (FStar_Pervasives_Native.fst ts1) in
                                      (let uu____1691 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1693 =
                                               FStar_Syntax_Util.is_unknown
                                                 (FStar_Pervasives_Native.snd
                                                    ts1) in
                                             Prims.op_Negation uu____1693))
                                           && (m <> n1) in
                                       if uu____1691
                                       then
                                         let error1 =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let err_msg =
                                           let uu____1709 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1710 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error1 uu____1709 uu____1710 in
                                         FStar_Exn.raise
                                           (FStar_Errors.Error
                                              (err_msg,
                                                ((FStar_Pervasives_Native.snd
                                                    ts1).FStar_Syntax_Syntax.pos)))
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1718 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1718 with
                                      | (univs2,defn) ->
                                          let uu____1725 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1725 with
                                           | (univs',typ) ->
                                               let uu___127_1735 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___127_1735.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___127_1735.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___127_1735.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___128_1740 = ed2 in
                                      let uu____1741 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1742 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1743 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1744 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1745 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1746 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1747 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1748 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1749 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1750 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1751 =
                                        let uu____1752 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1752 in
                                      let uu____1763 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1764 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1765 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___128_1740.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___128_1740.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1741;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1742;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1743;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1744;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1745;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1746;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1747;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1748;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1749;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1750;
                                        FStar_Syntax_Syntax.repr = uu____1751;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1763;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1764;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1765
                                      } in
                                    ((let uu____1769 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1769
                                      then
                                        let uu____1770 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1770
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
      let uu____1790 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1790 with
      | (effect_binders_un,signature_un) ->
          let uu____1807 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1807 with
           | (effect_binders,env1,uu____1826) ->
               let uu____1827 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1827 with
                | (signature,uu____1843) ->
                    let raise_error err_msg =
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           (err_msg, (signature.FStar_Syntax_Syntax.pos))) in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1871  ->
                           match uu____1871 with
                           | (bv,qual) ->
                               let uu____1882 =
                                 let uu___129_1883 = bv in
                                 let uu____1884 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___129_1883.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___129_1883.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1884
                                 } in
                               (uu____1882, qual)) effect_binders in
                    let uu____1887 =
                      let uu____1894 =
                        let uu____1895 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1895.FStar_Syntax_Syntax.n in
                      match uu____1894 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1905)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1927 ->
                          raise_error
                            "bad shape for effect-for-free signature" in
                    (match uu____1887 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1951 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1951
                           then
                             let uu____1952 =
                               let uu____1955 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1955 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1952
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1989 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1989 with
                           | (t2,comp,uu____2002) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2009 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2009 with
                          | (repr,_comp) ->
                              ((let uu____2031 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2031
                                then
                                  let uu____2032 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2032
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
                                  let uu____2038 =
                                    let uu____2039 =
                                      let uu____2040 =
                                        let uu____2055 =
                                          let uu____2062 =
                                            let uu____2067 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2068 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2067, uu____2068) in
                                          [uu____2062] in
                                        (wp_type1, uu____2055) in
                                      FStar_Syntax_Syntax.Tm_app uu____2040 in
                                    mk1 uu____2039 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2038 in
                                let effect_signature =
                                  let binders =
                                    let uu____2093 =
                                      let uu____2098 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2098) in
                                    let uu____2099 =
                                      let uu____2106 =
                                        let uu____2107 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2107
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2106] in
                                    uu____2093 :: uu____2099 in
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
                                  let uu____2170 = item in
                                  match uu____2170 with
                                  | (u_item,item1) ->
                                      let uu____2191 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2191 with
                                       | (item2,item_comp) ->
                                           ((let uu____2207 =
                                               let uu____2208 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2208 in
                                             if uu____2207
                                             then
                                               let uu____2209 =
                                                 let uu____2210 =
                                                   let uu____2211 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2212 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2211 uu____2212 in
                                                 FStar_Errors.Err uu____2210 in
                                               FStar_Exn.raise uu____2209
                                             else ());
                                            (let uu____2214 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2214 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2234 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2234 with
                                | (dmff_env1,uu____2258,bind_wp,bind_elab) ->
                                    let uu____2261 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2261 with
                                     | (dmff_env2,uu____2285,return_wp,return_elab)
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
                                           let uu____2292 =
                                             let uu____2293 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2293.FStar_Syntax_Syntax.n in
                                           match uu____2292 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2337 =
                                                 let uu____2352 =
                                                   let uu____2357 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2357 in
                                                 match uu____2352 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2421 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2337 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2460 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2460 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2477 =
                                                          let uu____2478 =
                                                            let uu____2493 =
                                                              let uu____2500
                                                                =
                                                                let uu____2505
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2506
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2505,
                                                                  uu____2506) in
                                                              [uu____2500] in
                                                            (wp_type1,
                                                              uu____2493) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2478 in
                                                        mk1 uu____2477 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2521 =
                                                      let uu____2530 =
                                                        let uu____2531 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2531 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2530 in
                                                    (match uu____2521 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2550
                                                           =
                                                           let error_msg =
                                                             let uu____2552 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2552
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
                                                                (let uu____2558
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
                                                                   uu____2558
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
                                                             let uu____2585 =
                                                               let uu____2586
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2587
                                                                 =
                                                                 let uu____2588
                                                                   =
                                                                   let uu____2595
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2595,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2588] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2586
                                                                 uu____2587 in
                                                             uu____2585
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2620 =
                                                             let uu____2621 =
                                                               let uu____2628
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2628] in
                                                             b11 ::
                                                               uu____2621 in
                                                           let uu____2633 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2620
                                                             uu____2633
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2634 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2636 =
                                             let uu____2637 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2637.FStar_Syntax_Syntax.n in
                                           match uu____2636 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2681 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2681
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2694 ->
                                               raise_error
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2696 =
                                             let uu____2697 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2697.FStar_Syntax_Syntax.n in
                                           match uu____2696 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2724 =
                                                 let uu____2725 =
                                                   let uu____2728 =
                                                     let uu____2729 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2729 in
                                                   [uu____2728] in
                                                 FStar_List.append uu____2725
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2724 body what
                                           | uu____2730 ->
                                               raise_error
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2748 =
                                                let uu____2749 =
                                                  let uu____2750 =
                                                    let uu____2765 =
                                                      let uu____2766 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2766 in
                                                    (t, uu____2765) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2750 in
                                                mk1 uu____2749 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2748) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2796 = f a2 in
                                               [uu____2796]
                                           | x::xs ->
                                               let uu____2801 =
                                                 apply_last1 f xs in
                                               x :: uu____2801 in
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
                                           let uu____2821 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2821 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2851 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2851
                                                 then
                                                   let uu____2852 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2852
                                                 else ());
                                                (let uu____2854 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2854))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2863 =
                                                 let uu____2868 = mk_lid name in
                                                 let uu____2869 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2868 uu____2869 in
                                               (match uu____2863 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2873 =
                                                        let uu____2876 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____2876 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____2873);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3011 =
                                             let uu____3014 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3015 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3014 :: uu____3015 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3011);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3151 =
                                               let uu____3154 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3155 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3154 :: uu____3155 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3151);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3288 =
                                                FStar_List.fold_left
                                                  (fun uu____3328  ->
                                                     fun action  ->
                                                       match uu____3328 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3349 =
                                                             let uu____3356 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3356
                                                               params_un in
                                                           (match uu____3349
                                                            with
                                                            | (action_params,env',uu____3365)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3385
                                                                     ->
                                                                    match uu____3385
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3396
                                                                    =
                                                                    let uu___130_3397
                                                                    = bv in
                                                                    let uu____3398
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___130_3397.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___130_3397.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3398
                                                                    } in
                                                                    (uu____3396,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3402
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3402
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
                                                                    uu____3432
                                                                    ->
                                                                    let uu____3433
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3433 in
                                                                    ((
                                                                    let uu____3437
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3437
                                                                    then
                                                                    let uu____3438
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3439
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3440
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3441
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3438
                                                                    uu____3439
                                                                    uu____3440
                                                                    uu____3441
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
                                                                    let uu____3445
                                                                    =
                                                                    let uu____3448
                                                                    =
                                                                    let uu___131_3449
                                                                    = action in
                                                                    let uu____3450
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3451
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___131_3449.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___131_3449.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___131_3449.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3450;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3451
                                                                    } in
                                                                    uu____3448
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3445))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3288 with
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
                                                      let uu____3484 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3485 =
                                                        let uu____3488 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3488] in
                                                      uu____3484 ::
                                                        uu____3485 in
                                                    let uu____3489 =
                                                      let uu____3490 =
                                                        let uu____3491 =
                                                          let uu____3492 =
                                                            let uu____3507 =
                                                              let uu____3514
                                                                =
                                                                let uu____3519
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3520
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3519,
                                                                  uu____3520) in
                                                              [uu____3514] in
                                                            (repr,
                                                              uu____3507) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3492 in
                                                        mk1 uu____3491 in
                                                      let uu____3535 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3490
                                                        uu____3535 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3489
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3538 =
                                                    let uu____3545 =
                                                      let uu____3546 =
                                                        let uu____3549 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3549 in
                                                      uu____3546.FStar_Syntax_Syntax.n in
                                                    match uu____3545 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3559)
                                                        ->
                                                        let uu____3588 =
                                                          let uu____3605 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3605
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3663 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3588
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3713 =
                                                               let uu____3714
                                                                 =
                                                                 let uu____3717
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3717 in
                                                               uu____3714.FStar_Syntax_Syntax.n in
                                                             (match uu____3713
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3742
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3742
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3755
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3780
                                                                     ->
                                                                    match uu____3780
                                                                    with
                                                                    | 
                                                                    (bv,uu____3786)
                                                                    ->
                                                                    let uu____3787
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3788
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3787
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3755
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
                                                                    let uu____3852
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3852 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg)
                                                                    | 
                                                                    uu____3857
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3865 in
                                                                    FStar_Exn.raise
                                                                    (FStar_Errors.Err
                                                                    err_msg) in
                                                                    let uu____3870
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3873
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3870,
                                                                    uu____3873)))
                                                              | uu____3880 ->
                                                                  let uu____3881
                                                                    =
                                                                    let uu____3882
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3882 in
                                                                  raise_error
                                                                    uu____3881))
                                                    | uu____3889 ->
                                                        let uu____3890 =
                                                          let uu____3891 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3891 in
                                                        raise_error
                                                          uu____3890 in
                                                  (match uu____3538 with
                                                   | (pre,post) ->
                                                       ((let uu____3915 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3917 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3919 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___132_3921
                                                             = ed in
                                                           let uu____3922 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3923 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3924 =
                                                             let uu____3925 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3925) in
                                                           let uu____3932 =
                                                             let uu____3933 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3933) in
                                                           let uu____3940 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3941 =
                                                             let uu____3942 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3942) in
                                                           let uu____3949 =
                                                             let uu____3950 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3950) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3922;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3923;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3924;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3932;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___132_3921.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3940;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3941;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3949;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3957 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3957
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3975
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3975
                                                               then
                                                                 let uu____3976
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3976
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
                                                                    let uu____3988
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    let uu____4000
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4000) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3991 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3988;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4015
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4015
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4017
                                                                 =
                                                                 let uu____4020
                                                                   =
                                                                   let uu____4023
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4023 in
                                                                 FStar_List.append
                                                                   uu____4020
                                                                   sigelts' in
                                                               (uu____4017,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4104 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4104 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4137 = FStar_List.hd ses in
            uu____4137.FStar_Syntax_Syntax.sigrng in
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
           | uu____4142 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Invalid (partial) redefinition of lex_t", err_range)));
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4147,uu____4148);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4150;
               FStar_Syntax_Syntax.sigattrs = uu____4151;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4155);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4157;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4158;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4162);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4164;
                 FStar_Syntax_Syntax.sigattrs = uu____4165;_}::[]
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
                 let uu____4230 =
                   let uu____4233 =
                     let uu____4234 =
                       let uu____4241 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4241, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4234 in
                   FStar_Syntax_Syntax.mk uu____4233 in
                 uu____4230 FStar_Pervasives_Native.None r1 in
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
                   let uu____4259 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4259 in
                 let hd1 =
                   let uu____4261 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4261 in
                 let tl1 =
                   let uu____4263 =
                     let uu____4264 =
                       let uu____4267 =
                         let uu____4268 =
                           let uu____4275 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4275, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4268 in
                       FStar_Syntax_Syntax.mk uu____4267 in
                     uu____4264 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4263 in
                 let res =
                   let uu____4284 =
                     let uu____4287 =
                       let uu____4288 =
                         let uu____4295 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4295,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4288 in
                     FStar_Syntax_Syntax.mk uu____4287 in
                   uu____4284 FStar_Pervasives_Native.None r2 in
                 let uu____4301 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4301 in
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
               let uu____4340 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4340;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4345 ->
               let err_msg =
                 let uu____4349 =
                   let uu____4350 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4350 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4349 in
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
            let uu____4380 = FStar_Syntax_Util.type_u () in
            match uu____4380 with
            | (k,uu____4386) ->
                let phi1 =
                  let uu____4388 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4388
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4390 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4390 with
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
          let uu____4436 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4436 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4469 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4469 FStar_List.flatten in
              ((let uu____4483 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4483
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
                          let uu____4494 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4504,uu____4505,uu____4506,uu____4507,uu____4508)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4517 -> failwith "Impossible!" in
                          match uu____4494 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4528 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4532,uu____4533,uu____4534,uu____4535,uu____4536)
                        -> lid
                    | uu____4545 -> failwith "Impossible" in
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
                  let uu____4563 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4563
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
                     let uu____4586 =
                       let uu____4589 =
                         let uu____4590 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4590;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4589 :: ses1 in
                     (uu____4586, data_ops_ses)) in
                (let uu____4600 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4636 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4661 ->
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
           let uu____4713 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4713 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4752 = FStar_Options.set_options t s in
             match uu____4752 with
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
                ((let uu____4778 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4778 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4786 = cps_and_elaborate env1 ne in
           (match uu____4786 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___133_4823 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___133_4823.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___133_4823.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___133_4823.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___133_4823.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___134_4825 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___134_4825.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___134_4825.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___134_4825.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___134_4825.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___135_4833 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___135_4833.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___135_4833.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___135_4833.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___135_4833.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4841 =
             let uu____4848 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4848 in
           (match uu____4841 with
            | (a,wp_a_src) ->
                let uu____4863 =
                  let uu____4870 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4870 in
                (match uu____4863 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4886 =
                         let uu____4889 =
                           let uu____4890 =
                             let uu____4897 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4897) in
                           FStar_Syntax_Syntax.NT uu____4890 in
                         [uu____4889] in
                       FStar_Syntax_Subst.subst uu____4886 wp_b_tgt in
                     let expected_k =
                       let uu____4901 =
                         let uu____4908 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4909 =
                           let uu____4912 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4912] in
                         uu____4908 :: uu____4909 in
                       let uu____4913 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4901 uu____4913 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4934 =
                           let uu____4935 =
                             let uu____4940 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4941 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4940, uu____4941) in
                           FStar_Errors.Error uu____4935 in
                         FStar_Exn.raise uu____4934 in
                       let uu____4944 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4944 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4976 =
                             let uu____4977 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4977 in
                           if uu____4976
                           then no_reify eff_name
                           else
                             (let uu____4983 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4984 =
                                let uu____4987 =
                                  let uu____4988 =
                                    let uu____5003 =
                                      let uu____5006 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5007 =
                                        let uu____5010 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5010] in
                                      uu____5006 :: uu____5007 in
                                    (repr, uu____5003) in
                                  FStar_Syntax_Syntax.Tm_app uu____4988 in
                                FStar_Syntax_Syntax.mk uu____4987 in
                              uu____4984 FStar_Pervasives_Native.None
                                uu____4983) in
                     let uu____5016 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5044,lift_wp)) ->
                           let uu____5068 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5068)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5094 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5094
                             then
                               let uu____5095 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5095
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____5098 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5098 with
                             | (lift1,comp,uu____5113) ->
                                 let uu____5114 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5114 with
                                  | (uu____5127,lift_wp,lift_elab) ->
                                      let uu____5130 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5131 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5016 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___136_5172 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___136_5172.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___136_5172.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___136_5172.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___136_5172.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___136_5172.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___136_5172.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___136_5172.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___136_5172.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___136_5172.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___136_5172.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___136_5172.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___136_5172.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___136_5172.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___136_5172.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___136_5172.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___136_5172.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___136_5172.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___136_5172.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___136_5172.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___136_5172.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___136_5172.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___136_5172.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___136_5172.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___136_5172.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___136_5172.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___136_5172.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___136_5172.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___136_5172.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___136_5172.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___136_5172.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___136_5172.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___136_5172.FStar_TypeChecker_Env.dsenv)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5178,lift1)
                                ->
                                let uu____5190 =
                                  let uu____5197 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5197 in
                                (match uu____5190 with
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
                                         let uu____5221 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5222 =
                                           let uu____5225 =
                                             let uu____5226 =
                                               let uu____5241 =
                                                 let uu____5244 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5245 =
                                                   let uu____5248 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5248] in
                                                 uu____5244 :: uu____5245 in
                                               (lift_wp1, uu____5241) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5226 in
                                           FStar_Syntax_Syntax.mk uu____5225 in
                                         uu____5222
                                           FStar_Pervasives_Native.None
                                           uu____5221 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5257 =
                                         let uu____5264 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5265 =
                                           let uu____5268 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5269 =
                                             let uu____5272 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5272] in
                                           uu____5268 :: uu____5269 in
                                         uu____5264 :: uu____5265 in
                                       let uu____5273 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5257
                                         uu____5273 in
                                     let uu____5276 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5276 with
                                      | (expected_k2,uu____5286,uu____5287)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___137_5290 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___137_5290.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___137_5290.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___138_5292 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___138_5292.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___138_5292.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___138_5292.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___138_5292.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5311 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5311 with
            | (tps1,c1) ->
                let uu____5326 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5326 with
                 | (tps2,env3,us) ->
                     let uu____5344 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5344 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5365 =
                              let uu____5366 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5366 in
                            match uu____5365 with
                            | (uvs1,t) ->
                                let uu____5381 =
                                  let uu____5394 =
                                    let uu____5399 =
                                      let uu____5400 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5400.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5399) in
                                  match uu____5394 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5415,c4)) -> ([], c4)
                                  | (uu____5455,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5482 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5381 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5526 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5526 with
                                         | (uu____5531,t1) ->
                                             let uu____5533 =
                                               let uu____5534 =
                                                 let uu____5539 =
                                                   let uu____5540 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5541 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5542 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5540 uu____5541
                                                     uu____5542 in
                                                 (uu____5539, r) in
                                               FStar_Errors.Error uu____5534 in
                                             FStar_Exn.raise uu____5533)
                                      else ();
                                      (let se1 =
                                         let uu___139_5545 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___139_5545.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___139_5545.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___139_5545.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___139_5545.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5562,uu____5563,uu____5564) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_5568  ->
                   match uu___114_5568 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5569 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5574,uu____5575) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___114_5583  ->
                   match uu___114_5583 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5584 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5594 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5594
             then
               let uu____5595 =
                 let uu____5596 =
                   let uu____5601 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5601, r) in
                 FStar_Errors.Error uu____5596 in
               FStar_Exn.raise uu____5595
             else ());
            (let uu____5603 =
               if uvs = []
               then
                 let uu____5604 =
                   let uu____5605 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5605 in
                 check_and_gen env2 t uu____5604
               else
                 (let uu____5611 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5611 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5619 =
                          let uu____5620 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5620 in
                        tc_check_trivial_guard env2 t1 uu____5619 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5626 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5626)) in
             match uu____5603 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___140_5642 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___140_5642.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___140_5642.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___140_5642.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___140_5642.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5652 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5652 with
            | (uu____5665,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5675 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5675 with
            | (e1,c,g1) ->
                let uu____5693 =
                  let uu____5700 =
                    let uu____5703 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5703 in
                  let uu____5704 =
                    let uu____5709 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5709) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5700 uu____5704 in
                (match uu____5693 with
                 | (e2,uu____5723,g) ->
                     ((let uu____5726 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5726);
                      (let se1 =
                         let uu___141_5728 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_5728.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_5728.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_5728.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___141_5728.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5779 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5779
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5787 =
                      let uu____5788 =
                        let uu____5793 =
                          let uu____5794 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5795 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5796 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5794 uu____5795 uu____5796 in
                        (uu____5793, r) in
                      FStar_Errors.Error uu____5788 in
                    FStar_Exn.raise uu____5787) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5822 =
                   let uu____5823 = FStar_Syntax_Subst.compress def in
                   uu____5823.FStar_Syntax_Syntax.n in
                 match uu____5822 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5833,uu____5834)
                     -> binders
                 | uu____5855 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5865;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5943) -> val_bs1
                     | (uu____5966,[]) -> val_bs1
                     | ((body_bv,uu____5990)::bt,(val_bv,aqual)::vt) ->
                         let uu____6027 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6043) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___142_6045 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___143_6048 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___143_6048.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___142_6045.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___142_6045.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6027 in
                   let uu____6049 =
                     let uu____6052 =
                       let uu____6053 =
                         let uu____6066 = rename_binders1 def_bs val_bs in
                         (uu____6066, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6053 in
                     FStar_Syntax_Syntax.mk uu____6052 in
                   uu____6049 FStar_Pervasives_Native.None r1
               | uu____6084 -> typ1 in
             let uu___144_6085 = lb in
             let uu____6086 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___144_6085.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___144_6085.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6086;
               FStar_Syntax_Syntax.lbeff =
                 (uu___144_6085.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___144_6085.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____6089 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6140  ->
                     fun lb  ->
                       match uu____6140 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6182 =
                             let uu____6193 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6193 with
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
                                   | uu____6278 ->
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
                                  (let uu____6321 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6321, quals_opt1))) in
                           (match uu____6182 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6089 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6415 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___115_6419  ->
                                match uu___115_6419 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6420 -> false)) in
                      if uu____6415
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6430 =
                    let uu____6433 =
                      let uu____6434 =
                        let uu____6447 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6447) in
                      FStar_Syntax_Syntax.Tm_let uu____6434 in
                    FStar_Syntax_Syntax.mk uu____6433 in
                  uu____6430 FStar_Pervasives_Native.None r in
                let uu____6465 =
                  let uu____6476 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___145_6485 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___145_6485.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___145_6485.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___145_6485.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___145_6485.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___145_6485.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___145_6485.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___145_6485.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___145_6485.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___145_6485.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___145_6485.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___145_6485.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___145_6485.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___145_6485.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___145_6485.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___145_6485.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___145_6485.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___145_6485.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___145_6485.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___145_6485.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___145_6485.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___145_6485.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___145_6485.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___145_6485.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___145_6485.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___145_6485.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___145_6485.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___145_6485.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___145_6485.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___145_6485.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___145_6485.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___145_6485.FStar_TypeChecker_Env.dsenv)
                       }) e in
                  match uu____6476 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6498;
                       FStar_Syntax_Syntax.vars = uu____6499;_},uu____6500,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6529 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6529) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6547,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6552 -> quals in
                      ((let uu___146_6560 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___146_6560.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___146_6560.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___146_6560.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6569 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6465 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6618 = log env2 in
                       if uu____6618
                       then
                         let uu____6619 =
                           let uu____6620 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6635 =
                                         let uu____6644 =
                                           let uu____6645 =
                                             let uu____6648 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6648.FStar_Syntax_Syntax.fv_name in
                                           uu____6645.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6644 in
                                       match uu____6635 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6655 -> false in
                                     if should_log
                                     then
                                       let uu____6664 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6665 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6664 uu____6665
                                     else "")) in
                           FStar_All.pipe_right uu____6620
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6619
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6696 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6696 with
                              | (bs1,c1) ->
                                  let uu____6703 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6703
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6715 =
                                            let uu____6716 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6716.FStar_Syntax_Syntax.n in
                                          (match uu____6715 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6741 =
                                                 let uu____6742 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6742.FStar_Syntax_Syntax.n in
                                               (match uu____6741 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6752 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6752 in
                                                    let uu____6753 =
                                                      let uu____6754 =
                                                        let uu____6755 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6755 args in
                                                      uu____6754
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6753 u
                                                | uu____6758 -> c1)
                                           | uu____6759 -> c1)
                                      | uu____6760 -> c1 in
                                    let uu___147_6761 = t1 in
                                    let uu____6762 =
                                      let uu____6763 =
                                        let uu____6776 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6776) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6763 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6762;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___147_6761.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___147_6761.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6800 =
                               let uu____6801 = FStar_Syntax_Subst.compress h in
                               uu____6801.FStar_Syntax_Syntax.n in
                             (match uu____6800 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6811 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6811 in
                                  let uu____6812 =
                                    let uu____6813 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6813
                                      args in
                                  uu____6812 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6816 -> t1)
                         | uu____6817 -> t1 in
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
                           let uu____6845 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6845 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6862 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6862, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6893 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6893 in
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
                         let uu___148_6900 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___149_6912 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___149_6912.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___149_6912.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___149_6912.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___149_6912.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___148_6900.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___148_6900.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___148_6900.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___148_6900.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6929 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6929 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6963 =
                                    let uu____6964 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6964.FStar_Syntax_Syntax.n in
                                  (match uu____6963 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6997 =
                                           let uu____7000 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____7000.FStar_Syntax_Syntax.fv_name in
                                         uu____6997.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____7002 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____7002 in
                                       let uu____7003 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____7003 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7013 =
                                              let uu____7014 =
                                                let uu____7015 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7015 in
                                              Prims.op_Negation uu____7014 in
                                            if uu____7013
                                            then
                                              ((let uu____7045 =
                                                  let uu____7046 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____7046 in
                                                if uu____7045
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
                                               (let uu____7153 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid in
                                                if uu____7153
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
                                   | uu____7182 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7187 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7209 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7209
                             then
                               let uu____7210 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7211 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7210 uu____7211
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
             (fun uu___116_7264  ->
                match uu___116_7264 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7265 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7271) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7277 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7286 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7291 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7316 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7340) ->
          let uu____7349 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7349
          then
            let for_export_bundle se1 uu____7380 =
              match uu____7380 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7419,uu____7420) ->
                       let dec =
                         let uu___150_7430 = se1 in
                         let uu____7431 =
                           let uu____7432 =
                             let uu____7439 =
                               let uu____7442 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7442 in
                             (l, us, uu____7439) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7432 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7431;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___150_7430.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___150_7430.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___150_7430.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7454,uu____7455,uu____7456) ->
                       let dec =
                         let uu___151_7462 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___151_7462.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___151_7462.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___151_7462.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7467 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7489,uu____7490,uu____7491) ->
          let uu____7492 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7492 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7513 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7513
          then
            ([(let uu___152_7529 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___152_7529.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___152_7529.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___152_7529.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7531 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___117_7535  ->
                       match uu___117_7535 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7536 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7541 -> true
                       | uu____7542 -> false)) in
             if uu____7531 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7560 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7565 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7570 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7575 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7580 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7598) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7615 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7615
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
          let uu____7646 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7646
          then
            let uu____7655 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___153_7668 = se in
                      let uu____7669 =
                        let uu____7670 =
                          let uu____7677 =
                            let uu____7678 =
                              let uu____7681 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7681.FStar_Syntax_Syntax.fv_name in
                            uu____7678.FStar_Syntax_Syntax.v in
                          (uu____7677, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7670 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7669;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___153_7668.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___153_7668.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___153_7668.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7655, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7703 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7720 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7735) ->
          let env1 =
            let uu____7739 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7739 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7741 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7742 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7752 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7752) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7753,uu____7754,uu____7755) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_7759  ->
                  match uu___118_7759 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7760 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7761,uu____7762) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_7770  ->
                  match uu___118_7770 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7771 -> false))
          -> env
      | uu____7772 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7834 se =
        match uu____7834 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7887 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7887
              then
                let uu____7888 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7888
              else ());
             (let uu____7890 = tc_decl env1 se in
              match uu____7890 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7940 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7940
                             then
                               let uu____7941 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7941
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
                    (let uu____7964 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7964
                     then
                       let uu____7965 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7971 =
                                  let uu____7972 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7972 "\n" in
                                Prims.strcat s uu____7971) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7965
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7977 =
                       let accum_exports_hidden uu____8007 se1 =
                         match uu____8007 with
                         | (exports1,hidden1) ->
                             let uu____8035 = for_export hidden1 se1 in
                             (match uu____8035 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7977 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___154_8114 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___154_8114.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___154_8114.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___154_8114.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___154_8114.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8192 = acc in
        match uu____8192 with
        | (uu____8227,uu____8228,env1,uu____8230) ->
            let uu____8243 =
              FStar_Util.record_time
                (fun uu____8289  -> process_one_decl acc se) in
            (match uu____8243 with
             | (r,ms_elapsed) ->
                 ((let uu____8353 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8353
                   then
                     let uu____8354 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8355 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8354 uu____8355
                   else ());
                  r)) in
      let uu____8357 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8357 with
      | (ses1,exports,env1,uu____8405) ->
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
        (let uu____8448 = FStar_Options.debug_any () in
         if uu____8448
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
           let uu___155_8454 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___155_8454.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___155_8454.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___155_8454.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___155_8454.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___155_8454.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___155_8454.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___155_8454.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___155_8454.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___155_8454.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___155_8454.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___155_8454.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___155_8454.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___155_8454.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___155_8454.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___155_8454.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___155_8454.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___155_8454.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___155_8454.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___155_8454.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___155_8454.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___155_8454.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___155_8454.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___155_8454.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___155_8454.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___155_8454.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___155_8454.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___155_8454.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___155_8454.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___155_8454.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___155_8454.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___155_8454.FStar_TypeChecker_Env.dsenv)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8458 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8458 with
          | (ses,exports,env3) ->
              ((let uu___156_8491 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___156_8491.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___156_8491.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___156_8491.FStar_Syntax_Syntax.is_interface)
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
        let uu____8516 = tc_decls env decls in
        match uu____8516 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___157_8547 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___157_8547.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___157_8547.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___157_8547.FStar_Syntax_Syntax.is_interface)
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
          let uu___158_8567 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___158_8567.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___158_8567.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___158_8567.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___158_8567.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___158_8567.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___158_8567.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___158_8567.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___158_8567.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___158_8567.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___158_8567.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___158_8567.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___158_8567.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___158_8567.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___158_8567.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___158_8567.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___158_8567.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___158_8567.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___158_8567.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___158_8567.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___158_8567.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___158_8567.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___158_8567.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___158_8567.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___158_8567.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___158_8567.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___158_8567.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___158_8567.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___158_8567.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___158_8567.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___158_8567.FStar_TypeChecker_Env.dsenv)
          } in
        let check_term1 lid univs1 t =
          let uu____8578 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8578 with
          | (univs2,t1) ->
              ((let uu____8586 =
                  let uu____8587 =
                    let uu____8590 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8590 in
                  FStar_All.pipe_left uu____8587
                    (FStar_Options.Other "Exports") in
                if uu____8586
                then
                  let uu____8591 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8592 =
                    let uu____8593 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8593
                      (FStar_String.concat ", ") in
                  let uu____8602 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8591 uu____8592 uu____8602
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8605 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8605 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8629 =
             let uu____8630 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8631 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8630 uu____8631 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8629);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8638) ->
              let uu____8647 =
                let uu____8648 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8648 in
              if uu____8647
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8658,uu____8659) ->
              let t =
                let uu____8671 =
                  let uu____8674 =
                    let uu____8675 =
                      let uu____8688 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8688) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8675 in
                  FStar_Syntax_Syntax.mk uu____8674 in
                uu____8671 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8695,uu____8696,uu____8697) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8705 =
                let uu____8706 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8706 in
              if uu____8705 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8710,lbs),uu____8712) ->
              let uu____8727 =
                let uu____8728 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8728 in
              if uu____8727
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
              let uu____8747 =
                let uu____8748 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8748 in
              if uu____8747
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8755 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8756 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8763 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8764 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8765 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8766 -> () in
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
      (let uu____8782 =
         let uu____8783 = FStar_Options.interactive () in
         Prims.op_Negation uu____8783 in
       if uu____8782
       then
         let uu____8784 = FStar_Options.restore_cmd_line_options true in
         FStar_All.pipe_right uu____8784 FStar_Pervasives.ignore
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
          let uu___159_8803 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___159_8803.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___159_8803.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8806 =
           let uu____8807 = FStar_Options.lax () in
           Prims.op_Negation uu____8807 in
         if uu____8806 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8813 =
           let uu____8814 = FStar_Options.interactive () in
           Prims.op_Negation uu____8814 in
         if uu____8813
         then
           let uu____8815 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8815 FStar_Pervasives.ignore
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
      let uu____8829 = tc_partial_modul env modul true in
      match uu____8829 with
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
      (let uu____8862 = FStar_Options.debug_any () in
       if uu____8862
       then
         let uu____8863 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8863
       else ());
      (let env1 =
         let uu___160_8867 = env in
         let uu____8868 =
           let uu____8869 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8869 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___160_8867.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___160_8867.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___160_8867.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___160_8867.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___160_8867.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___160_8867.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___160_8867.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___160_8867.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___160_8867.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___160_8867.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___160_8867.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___160_8867.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___160_8867.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___160_8867.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___160_8867.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___160_8867.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___160_8867.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___160_8867.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8868;
           FStar_TypeChecker_Env.lax_universes =
             (uu___160_8867.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___160_8867.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___160_8867.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___160_8867.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___160_8867.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___160_8867.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___160_8867.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___160_8867.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___160_8867.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___160_8867.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___160_8867.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___160_8867.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___160_8867.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___160_8867.FStar_TypeChecker_Env.dsenv)
         } in
       let uu____8870 = tc_modul env1 m in
       match uu____8870 with
       | (m1,env2) ->
           ((let uu____8882 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8882
             then
               let uu____8883 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8883
             else ());
            (let uu____8886 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8886
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
                       let uu____8917 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8917 with
                       | (univnames1,e) ->
                           let uu___161_8924 = lb in
                           let uu____8925 =
                             let uu____8928 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8928 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___161_8924.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___161_8924.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___161_8924.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___161_8924.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8925
                           } in
                     let uu___162_8929 = se in
                     let uu____8930 =
                       let uu____8931 =
                         let uu____8938 =
                           let uu____8945 = FStar_List.map update lbs in
                           (b, uu____8945) in
                         (uu____8938, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8931 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8930;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___162_8929.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___162_8929.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___162_8929.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___162_8929.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8958 -> se in
               let normalized_module =
                 let uu___163_8960 = m1 in
                 let uu____8961 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___163_8960.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8961;
                   FStar_Syntax_Syntax.exports =
                     (uu___163_8960.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___163_8960.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8962 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8962
             else ());
            (m1, env2)))