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
          let uu___95_15 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___95_15.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___95_15.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___95_15.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___95_15.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___95_15.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___95_15.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___95_15.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___95_15.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___95_15.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___95_15.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___95_15.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___95_15.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___95_15.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___95_15.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___95_15.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___95_15.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___95_15.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___95_15.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___95_15.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___95_15.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___95_15.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.type_of =
              (uu___95_15.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___95_15.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___95_15.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___95_15.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___95_15.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___95_15.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___95_15.FStar_TypeChecker_Env.identifier_info)
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
          let uu___96_31 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___96_31.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___96_31.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___96_31.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___96_31.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___96_31.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___96_31.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___96_31.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___96_31.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___96_31.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___96_31.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___96_31.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___96_31.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___96_31.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___96_31.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___96_31.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___96_31.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___96_31.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___96_31.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___96_31.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___96_31.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___96_31.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.type_of =
              (uu___96_31.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___96_31.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___96_31.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___96_31.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___96_31.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___96_31.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___96_31.FStar_TypeChecker_Env.identifier_info)
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
                      let uu___97_361 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___97_361.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___97_361.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___97_361.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___97_361.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___97_361.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___97_361.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___97_361.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___97_361.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___97_361.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___97_361.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___97_361.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___97_361.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___97_361.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___97_361.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___97_361.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___97_361.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___97_361.FStar_Syntax_Syntax.actions)
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
                          let uu___98_398 = ed1 in
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
                                 let uu___99_431 = a in
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
                                     (uu___99_431.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___99_431.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___99_431.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___99_431.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____432;
                                   FStar_Syntax_Syntax.action_typ = uu____444
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___98_398.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___98_398.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___98_398.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___98_398.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___98_398.FStar_Syntax_Syntax.signature);
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
                                              let uu___100_1280 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___100_1280.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___100_1280.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___100_1280.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.failhard
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.failhard);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___100_1280.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.is_native_tactic);
                                                FStar_TypeChecker_Env.identifier_info
                                                  =
                                                  (uu___100_1280.FStar_TypeChecker_Env.identifier_info)
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
                                           let uu___101_1413 =
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
                                               (uu___101_1413.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___101_1413.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___101_1413.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___101_1413.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___101_1413.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___101_1413.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___101_1413.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___101_1413.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___101_1413.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___101_1413.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___101_1413.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.failhard =
                                               (uu___101_1413.FStar_TypeChecker_Env.failhard);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___101_1413.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___101_1413.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___101_1413.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.is_native_tactic);
                                             FStar_TypeChecker_Env.identifier_info
                                               =
                                               (uu___101_1413.FStar_TypeChecker_Env.identifier_info)
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
                                                            failwith "" in
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
                                                          let uu___102_1599 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___102_1599.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___102_1599.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___102_1599.FStar_Syntax_Syntax.action_params);
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
                                      | uu____1673 -> failwith "Impossible" in
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
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         let uu____1708 =
                                           let uu____1709 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1710 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1709 uu____1710 in
                                         failwith uu____1708
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1716 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1716 with
                                      | (univs2,defn) ->
                                          let uu____1723 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1723 with
                                           | (univs',typ) ->
                                               let uu___103_1733 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___103_1733.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___103_1733.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___103_1733.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
                                      let uu___104_1738 = ed2 in
                                      let uu____1739 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1740 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1741 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1742 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1743 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1744 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1745 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1746 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1747 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1748 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1749 =
                                        let uu____1750 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        FStar_Pervasives_Native.snd
                                          uu____1750 in
                                      let uu____1761 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1762 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1763 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___104_1738.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___104_1738.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1739;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1740;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1741;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1742;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1743;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1744;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1745;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1746;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1747;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1748;
                                        FStar_Syntax_Syntax.repr = uu____1749;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1761;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1762;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1763
                                      } in
                                    ((let uu____1767 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
                                      if uu____1767
                                      then
                                        let uu____1768 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1768
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
      let uu____1788 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1788 with
      | (effect_binders_un,signature_un) ->
          let uu____1805 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1805 with
           | (effect_binders,env1,uu____1824) ->
               let uu____1825 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1825 with
                | (signature,uu____1841) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1861  ->
                           match uu____1861 with
                           | (bv,qual) ->
                               let uu____1872 =
                                 let uu___105_1873 = bv in
                                 let uu____1874 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___105_1873.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___105_1873.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1874
                                 } in
                               (uu____1872, qual)) effect_binders in
                    let uu____1877 =
                      let uu____1884 =
                        let uu____1885 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1885.FStar_Syntax_Syntax.n in
                      match uu____1884 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1895)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1917 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1877 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1941 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1941
                           then
                             let uu____1942 =
                               let uu____1945 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____1945 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1942
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____1979 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1979 with
                           | (t2,comp,uu____1992) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1999 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1999 with
                          | (repr,_comp) ->
                              ((let uu____2021 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2021
                                then
                                  let uu____2022 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2022
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
                                  let uu____2028 =
                                    let uu____2029 =
                                      let uu____2030 =
                                        let uu____2045 =
                                          let uu____2052 =
                                            let uu____2057 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2058 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2057, uu____2058) in
                                          [uu____2052] in
                                        (wp_type1, uu____2045) in
                                      FStar_Syntax_Syntax.Tm_app uu____2030 in
                                    mk1 uu____2029 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2028 in
                                let effect_signature =
                                  let binders =
                                    let uu____2083 =
                                      let uu____2088 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2088) in
                                    let uu____2089 =
                                      let uu____2096 =
                                        let uu____2097 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2097
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2096] in
                                    uu____2083 :: uu____2089 in
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
                                  let uu____2160 = item in
                                  match uu____2160 with
                                  | (u_item,item1) ->
                                      let uu____2181 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2181 with
                                       | (item2,item_comp) ->
                                           ((let uu____2197 =
                                               let uu____2198 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2198 in
                                             if uu____2197
                                             then
                                               let uu____2199 =
                                                 let uu____2200 =
                                                   let uu____2201 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2202 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2201 uu____2202 in
                                                 FStar_Errors.Err uu____2200 in
                                               FStar_Exn.raise uu____2199
                                             else ());
                                            (let uu____2204 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2204 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2224 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2224 with
                                | (dmff_env1,uu____2248,bind_wp,bind_elab) ->
                                    let uu____2251 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2251 with
                                     | (dmff_env2,uu____2275,return_wp,return_elab)
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
                                           let uu____2282 =
                                             let uu____2283 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2283.FStar_Syntax_Syntax.n in
                                           match uu____2282 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2327 =
                                                 let uu____2342 =
                                                   let uu____2347 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2347 in
                                                 match uu____2342 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2411 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2327 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2450 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2450 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2467 =
                                                          let uu____2468 =
                                                            let uu____2483 =
                                                              let uu____2490
                                                                =
                                                                let uu____2495
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2496
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2495,
                                                                  uu____2496) in
                                                              [uu____2490] in
                                                            (wp_type1,
                                                              uu____2483) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2468 in
                                                        mk1 uu____2467 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2511 =
                                                      let uu____2520 =
                                                        let uu____2521 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2521 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2520 in
                                                    (match uu____2511 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____2540
                                                           =
                                                           let error_msg =
                                                             let uu____2542 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2542
                                                               (match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           failwith error_msg in
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
                                                                (let uu____2548
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
                                                                   uu____2548
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
                                                             let uu____2575 =
                                                               let uu____2576
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____2577
                                                                 =
                                                                 let uu____2578
                                                                   =
                                                                   let uu____2585
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____2585,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____2578] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____2576
                                                                 uu____2577 in
                                                             uu____2575
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____2610 =
                                                             let uu____2611 =
                                                               let uu____2618
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2618] in
                                                             b11 ::
                                                               uu____2611 in
                                                           let uu____2623 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2610
                                                             uu____2623
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____2624 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____2626 =
                                             let uu____2627 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2627.FStar_Syntax_Syntax.n in
                                           match uu____2626 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2671 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2671
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____2684 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____2686 =
                                             let uu____2687 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2687.FStar_Syntax_Syntax.n in
                                           match uu____2686 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____2714 =
                                                 let uu____2715 =
                                                   let uu____2718 =
                                                     let uu____2719 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2719 in
                                                   [uu____2718] in
                                                 FStar_List.append uu____2715
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2714 body what
                                           | uu____2720 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2738 =
                                                let uu____2739 =
                                                  let uu____2740 =
                                                    let uu____2755 =
                                                      let uu____2756 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2756 in
                                                    (t, uu____2755) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2740 in
                                                mk1 uu____2739 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2738) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2786 = f a2 in
                                               [uu____2786]
                                           | x::xs ->
                                               let uu____2791 =
                                                 apply_last1 f xs in
                                               x :: uu____2791 in
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
                                           let uu____2811 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2811 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____2841 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2841
                                                 then
                                                   let uu____2842 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2842
                                                 else ());
                                                (let uu____2844 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____2844))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____2853 =
                                                 let uu____2858 = mk_lid name in
                                                 let uu____2859 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____2858 uu____2859 in
                                               (match uu____2853 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2863 =
                                                        let uu____2866 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____2866 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____2863);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         ((let uu____2936 =
                                             let uu____2939 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____2940 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____2939 :: uu____2940 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____2936);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____3009 =
                                              let uu____3012 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
                                              let uu____3013 =
                                                FStar_ST.op_Bang sigelts in
                                              uu____3012 :: uu____3013 in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____3009);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____3082 =
                                               let uu____3085 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3086 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3085 :: uu____3086 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3082);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____3155 =
                                                let uu____3158 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
                                                let uu____3159 =
                                                  FStar_ST.op_Bang sigelts in
                                                uu____3158 :: uu____3159 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____3155);
                                             (let uu____3226 =
                                                FStar_List.fold_left
                                                  (fun uu____3266  ->
                                                     fun action  ->
                                                       match uu____3266 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3287 =
                                                             let uu____3294 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3294
                                                               params_un in
                                                           (match uu____3287
                                                            with
                                                            | (action_params,env',uu____3303)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3323
                                                                     ->
                                                                    match uu____3323
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3334
                                                                    =
                                                                    let uu___106_3335
                                                                    = bv in
                                                                    let uu____3336
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___106_3335.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___106_3335.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3336
                                                                    } in
                                                                    (uu____3334,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3340
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3340
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
                                                                    uu____3370
                                                                    ->
                                                                    let uu____3371
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3371 in
                                                                    ((
                                                                    let uu____3375
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3375
                                                                    then
                                                                    let uu____3376
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3377
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3378
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3379
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3376
                                                                    uu____3377
                                                                    uu____3378
                                                                    uu____3379
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
                                                                    let uu____3383
                                                                    =
                                                                    let uu____3386
                                                                    =
                                                                    let uu___107_3387
                                                                    = action in
                                                                    let uu____3388
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3389
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___107_3387.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___107_3387.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___107_3387.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3388;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3389
                                                                    } in
                                                                    uu____3386
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3383))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3226 with
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
                                                      let uu____3422 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3423 =
                                                        let uu____3426 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3426] in
                                                      uu____3422 ::
                                                        uu____3423 in
                                                    let uu____3427 =
                                                      let uu____3428 =
                                                        let uu____3429 =
                                                          let uu____3430 =
                                                            let uu____3445 =
                                                              let uu____3452
                                                                =
                                                                let uu____3457
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3458
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3457,
                                                                  uu____3458) in
                                                              [uu____3452] in
                                                            (repr,
                                                              uu____3445) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3430 in
                                                        mk1 uu____3429 in
                                                      let uu____3473 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3428
                                                        uu____3473 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3427
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3476 =
                                                    let uu____3483 =
                                                      let uu____3484 =
                                                        let uu____3487 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3487 in
                                                      uu____3484.FStar_Syntax_Syntax.n in
                                                    match uu____3483 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____3497)
                                                        ->
                                                        let uu____3526 =
                                                          let uu____3543 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____3543
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____3601 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____3526
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____3651 =
                                                               let uu____3652
                                                                 =
                                                                 let uu____3655
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____3655 in
                                                               uu____3652.FStar_Syntax_Syntax.n in
                                                             (match uu____3651
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____3680
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____3680
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3693
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3718
                                                                     ->
                                                                    match uu____3718
                                                                    with
                                                                    | 
                                                                    (bv,uu____3724)
                                                                    ->
                                                                    let uu____3725
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3726
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3725
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3693
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
                                                                    uu____3785
                                                                    ->
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3793
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____3793 in
                                                                    failwith
                                                                    uu____3792 in
                                                                    let uu____3798
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3801
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3798,
                                                                    uu____3801)))
                                                              | uu____3808 ->
                                                                  let uu____3809
                                                                    =
                                                                    let uu____3810
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3810 in
                                                                  failwith
                                                                    uu____3809))
                                                    | uu____3817 ->
                                                        let uu____3818 =
                                                          let uu____3819 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____3819 in
                                                        failwith uu____3818 in
                                                  (match uu____3476 with
                                                   | (pre,post) ->
                                                       ((let uu____3843 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3845 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3847 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___108_3849
                                                             = ed in
                                                           let uu____3850 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3851 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3852 =
                                                             let uu____3853 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3853) in
                                                           let uu____3860 =
                                                             let uu____3861 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____3861) in
                                                           let uu____3868 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____3869 =
                                                             let uu____3870 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____3870) in
                                                           let uu____3877 =
                                                             let uu____3878 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____3878) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3850;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3851;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3852;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____3860;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___108_3849.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3868;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____3869;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____3877;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____3885 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____3885
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3903
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____3903
                                                               then
                                                                 let uu____3904
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____3904
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
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3919
                                                                    =
                                                                    let uu____3928
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____3928) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3919 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3916;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____3943
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3943
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____3945
                                                                 =
                                                                 let uu____3948
                                                                   =
                                                                   let uu____3951
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____3951 in
                                                                 FStar_List.append
                                                                   uu____3948
                                                                   sigelts' in
                                                               (uu____3945,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4000 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4000 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          match ses with
          | {
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (lex_t1,[],[],t,uu____4043,uu____4044);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____4046;
              FStar_Syntax_Syntax.sigattrs = uu____4047;_}::{
                                                              FStar_Syntax_Syntax.sigel
                                                                =
                                                                FStar_Syntax_Syntax.Sig_datacon
                                                                (lex_top1,[],_t_top,_lex_t_top,_0_41,uu____4051);
                                                              FStar_Syntax_Syntax.sigrng
                                                                = r1;
                                                              FStar_Syntax_Syntax.sigquals
                                                                = [];
                                                              FStar_Syntax_Syntax.sigmeta
                                                                = uu____4053;
                                                              FStar_Syntax_Syntax.sigattrs
                                                                = uu____4054;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_42,uu____4058);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____4060;
                FStar_Syntax_Syntax.sigattrs = uu____4061;_}::[]
              when
              ((_0_41 = (Prims.parse_int "0")) &&
                 (_0_42 = (Prims.parse_int "0")))
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
                  (FStar_Pervasives_Native.Some r) in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
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
                let uu____4126 =
                  let uu____4129 =
                    let uu____4130 =
                      let uu____4137 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None in
                      (uu____4137, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____4130 in
                  FStar_Syntax_Syntax.mk uu____4129 in
                uu____4126 FStar_Pervasives_Native.None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
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
                } in
              let ucons1 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let ucons2 =
                FStar_Syntax_Syntax.new_univ_name
                  (FStar_Pervasives_Native.Some r2) in
              let lex_cons_t =
                let a =
                  let uu____4155 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1))
                      FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4155 in
                let hd1 =
                  let uu____4157 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4157 in
                let tl1 =
                  let uu____4159 =
                    let uu____4160 =
                      let uu____4163 =
                        let uu____4164 =
                          let uu____4171 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant
                              FStar_Pervasives_Native.None in
                          (uu____4171, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____4164 in
                      FStar_Syntax_Syntax.mk uu____4163 in
                    uu____4160 FStar_Pervasives_Native.None r2 in
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some r2) uu____4159 in
                let res =
                  let uu____4180 =
                    let uu____4183 =
                      let uu____4184 =
                        let uu____4191 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None in
                        (uu____4191,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____4184 in
                    FStar_Syntax_Syntax.mk uu____4183 in
                  uu____4180 FStar_Pervasives_Native.None r2 in
                let uu____4197 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a,
                     (FStar_Pervasives_Native.Some
                        FStar_Syntax_Syntax.imp_tag));
                  (hd1, FStar_Pervasives_Native.None);
                  (tl1, FStar_Pervasives_Native.None)] uu____4197 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
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
                } in
              let uu____4236 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____4236;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }
          | uu____4241 ->
              let uu____4244 =
                let uu____4245 =
                  let uu____4246 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____4246 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____4245 in
              failwith uu____4244
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
            let uu____4276 = FStar_Syntax_Util.type_u () in
            match uu____4276 with
            | (k,uu____4282) ->
                let phi1 =
                  let uu____4284 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4284
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4286 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4286 with
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
          let uu____4332 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4332 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4365 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4365 FStar_List.flatten in
              ((let uu____4379 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4379
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
                          let uu____4390 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4400,uu____4401,uu____4402,uu____4403,uu____4404)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4413 -> failwith "Impossible!" in
                          match uu____4390 with
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____4424 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4428,uu____4429,uu____4430,uu____4431,uu____4432)
                        -> lid
                    | uu____4441 -> failwith "Impossible" in
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
                  let uu____4459 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4459
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
                     let uu____4482 =
                       let uu____4485 =
                         let uu____4486 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4486;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4485 :: ses1 in
                     (uu____4482, data_ops_ses)) in
                (let uu____4496 =
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4532 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4557 ->
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
           let uu____4609 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4609 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____4648 = FStar_Options.set_options t s in
             match uu____4648 with
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
                ((let uu____4674 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____4674 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4682 = cps_and_elaborate env1 ne in
           (match uu____4682 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___109_4719 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___109_4719.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___109_4719.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___109_4719.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___109_4719.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___110_4721 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___110_4721.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___110_4721.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___110_4721.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___110_4721.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___111_4729 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___111_4729.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___111_4729.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___111_4729.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___111_4729.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4737 =
             let uu____4744 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4744 in
           (match uu____4737 with
            | (a,wp_a_src) ->
                let uu____4759 =
                  let uu____4766 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4766 in
                (match uu____4759 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4782 =
                         let uu____4785 =
                           let uu____4786 =
                             let uu____4793 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4793) in
                           FStar_Syntax_Syntax.NT uu____4786 in
                         [uu____4785] in
                       FStar_Syntax_Subst.subst uu____4782 wp_b_tgt in
                     let expected_k =
                       let uu____4797 =
                         let uu____4804 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4805 =
                           let uu____4808 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4808] in
                         uu____4804 :: uu____4805 in
                       let uu____4809 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4797 uu____4809 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4830 =
                           let uu____4831 =
                             let uu____4836 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____4837 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____4836, uu____4837) in
                           FStar_Errors.Error uu____4831 in
                         FStar_Exn.raise uu____4830 in
                       let uu____4840 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4840 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4872 =
                             let uu____4873 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4873 in
                           if uu____4872
                           then no_reify eff_name
                           else
                             (let uu____4879 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4880 =
                                let uu____4883 =
                                  let uu____4884 =
                                    let uu____4899 =
                                      let uu____4902 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____4903 =
                                        let uu____4906 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____4906] in
                                      uu____4902 :: uu____4903 in
                                    (repr, uu____4899) in
                                  FStar_Syntax_Syntax.Tm_app uu____4884 in
                                FStar_Syntax_Syntax.mk uu____4883 in
                              uu____4880 FStar_Pervasives_Native.None
                                uu____4879) in
                     let uu____4912 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____4940,lift_wp)) ->
                           let uu____4964 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____4964)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____4990 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____4990
                             then
                               let uu____4991 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____4991
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
                             let uu____4994 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____4994 with
                             | (lift1,comp,uu____5009) ->
                                 let uu____5010 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5010 with
                                  | (uu____5023,lift_wp,lift_elab) ->
                                      let uu____5026 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5027 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____4912 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___112_5068 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___112_5068.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___112_5068.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___112_5068.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___112_5068.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___112_5068.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___112_5068.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___112_5068.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___112_5068.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___112_5068.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___112_5068.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___112_5068.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___112_5068.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___112_5068.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___112_5068.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___112_5068.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___112_5068.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___112_5068.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___112_5068.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___112_5068.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___112_5068.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.type_of =
                                (uu___112_5068.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___112_5068.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___112_5068.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___112_5068.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___112_5068.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___112_5068.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___112_5068.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___112_5068.FStar_TypeChecker_Env.identifier_info)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5074,lift1)
                                ->
                                let uu____5086 =
                                  let uu____5093 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5093 in
                                (match uu____5086 with
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
                                         let uu____5117 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5118 =
                                           let uu____5121 =
                                             let uu____5122 =
                                               let uu____5137 =
                                                 let uu____5140 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5141 =
                                                   let uu____5144 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5144] in
                                                 uu____5140 :: uu____5141 in
                                               (lift_wp1, uu____5137) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5122 in
                                           FStar_Syntax_Syntax.mk uu____5121 in
                                         uu____5118
                                           FStar_Pervasives_Native.None
                                           uu____5117 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5153 =
                                         let uu____5160 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5161 =
                                           let uu____5164 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5165 =
                                             let uu____5168 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5168] in
                                           uu____5164 :: uu____5165 in
                                         uu____5160 :: uu____5161 in
                                       let uu____5169 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5153
                                         uu____5169 in
                                     let uu____5172 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5172 with
                                      | (expected_k2,uu____5182,uu____5183)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___113_5186 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___113_5186.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___113_5186.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___114_5188 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___114_5188.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___114_5188.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___114_5188.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___114_5188.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5207 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5207 with
            | (tps1,c1) ->
                let uu____5222 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5222 with
                 | (tps2,env3,us) ->
                     let uu____5240 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5240 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5261 =
                              let uu____5262 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5262 in
                            match uu____5261 with
                            | (uvs1,t) ->
                                let uu____5277 =
                                  let uu____5290 =
                                    let uu____5295 =
                                      let uu____5296 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5296.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5295) in
                                  match uu____5290 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5311,c4)) -> ([], c4)
                                  | (uu____5351,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5378 -> failwith "Impossible" in
                                (match uu____5277 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5422 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5422 with
                                         | (uu____5427,t1) ->
                                             let uu____5429 =
                                               let uu____5430 =
                                                 let uu____5435 =
                                                   let uu____5436 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____5437 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
                                                   let uu____5438 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____5436 uu____5437
                                                     uu____5438 in
                                                 (uu____5435, r) in
                                               FStar_Errors.Error uu____5430 in
                                             FStar_Exn.raise uu____5429)
                                      else ();
                                      (let se1 =
                                         let uu___115_5441 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___115_5441.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___115_5441.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___115_5441.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___115_5441.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5458,uu____5459,uu____5460) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5464  ->
                   match uu___89_5464 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5465 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5470,uu____5471) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___89_5479  ->
                   match uu___89_5479 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5480 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5490 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5490
             then
               let uu____5491 =
                 let uu____5492 =
                   let uu____5497 =
                     FStar_Util.format1
                       "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                       (FStar_Ident.text_of_lid lid) in
                   (uu____5497, r) in
                 FStar_Errors.Error uu____5492 in
               FStar_Exn.raise uu____5491
             else ());
            (let uu____5499 =
               if uvs = []
               then
                 let uu____5500 =
                   let uu____5501 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5501 in
                 check_and_gen env2 t uu____5500
               else
                 (let uu____5507 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5507 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5515 =
                          let uu____5516 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5516 in
                        tc_check_trivial_guard env2 t1 uu____5515 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5522 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5522)) in
             match uu____5499 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___116_5538 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___116_5538.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___116_5538.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___116_5538.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___116_5538.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5548 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5548 with
            | (uu____5561,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5571 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5571 with
            | (e1,c,g1) ->
                let uu____5589 =
                  let uu____5596 =
                    let uu____5599 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5599 in
                  let uu____5600 =
                    let uu____5605 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____5605) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5596 uu____5600 in
                (match uu____5589 with
                 | (e2,uu____5619,g) ->
                     ((let uu____5622 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5622);
                      (let se1 =
                         let uu___117_5624 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_5624.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_5624.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_5624.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___117_5624.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5675 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5675
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5683 =
                      let uu____5684 =
                        let uu____5689 =
                          let uu____5690 = FStar_Syntax_Print.lid_to_string l in
                          let uu____5691 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____5692 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____5690 uu____5691 uu____5692 in
                        (uu____5689, r) in
                      FStar_Errors.Error uu____5684 in
                    FStar_Exn.raise uu____5683) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5718 =
                   let uu____5719 = FStar_Syntax_Subst.compress def in
                   uu____5719.FStar_Syntax_Syntax.n in
                 match uu____5718 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5729,uu____5730)
                     -> binders
                 | uu____5751 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5761;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5839) -> val_bs1
                     | (uu____5862,[]) -> val_bs1
                     | ((body_bv,uu____5886)::bt,(val_bv,aqual)::vt) ->
                         let uu____5923 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____5939) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___118_5941 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___119_5944 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___119_5944.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___118_5941.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___118_5941.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____5923 in
                   let uu____5945 =
                     let uu____5948 =
                       let uu____5949 =
                         let uu____5962 = rename_binders1 def_bs val_bs in
                         (uu____5962, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____5949 in
                     FStar_Syntax_Syntax.mk uu____5948 in
                   uu____5945 FStar_Pervasives_Native.None r1
               | uu____5980 -> typ1 in
             let uu___120_5981 = lb in
             let uu____5982 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___120_5981.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___120_5981.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____5982;
               FStar_Syntax_Syntax.lbeff =
                 (uu___120_5981.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___120_5981.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____5985 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6036  ->
                     fun lb  ->
                       match uu____6036 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6078 =
                             let uu____6089 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6089 with
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
                                   | uu____6174 ->
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
                                  (let uu____6217 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6217, quals_opt1))) in
                           (match uu____6078 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____5985 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6311 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___90_6315  ->
                                match uu___90_6315 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6316 -> false)) in
                      if uu____6311
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6326 =
                    let uu____6329 =
                      let uu____6330 =
                        let uu____6343 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6343) in
                      FStar_Syntax_Syntax.Tm_let uu____6330 in
                    FStar_Syntax_Syntax.mk uu____6329 in
                  uu____6326 FStar_Pervasives_Native.None r in
                let uu____6361 =
                  let uu____6372 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___121_6381 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___121_6381.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___121_6381.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___121_6381.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___121_6381.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___121_6381.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___121_6381.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___121_6381.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___121_6381.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___121_6381.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___121_6381.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___121_6381.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___121_6381.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___121_6381.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___121_6381.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___121_6381.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___121_6381.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___121_6381.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___121_6381.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___121_6381.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.type_of =
                           (uu___121_6381.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___121_6381.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___121_6381.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___121_6381.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___121_6381.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___121_6381.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___121_6381.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___121_6381.FStar_TypeChecker_Env.identifier_info)
                       }) e in
                  match uu____6372 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6394;
                       FStar_Syntax_Syntax.vars = uu____6395;_},uu____6396,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6425 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6425) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6443,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6448 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___91_6454  ->
                             match uu___91_6454 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____6457 =
                                   let uu____6458 =
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
                                            (let uu____6465 =
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
                                               uu____6465)
                                          else ();
                                          ok)
                                       (FStar_Pervasives_Native.snd lbs2) in
                                   Prims.op_Negation uu____6458 in
                                 if uu____6457
                                 then FStar_Pervasives_Native.None
                                 else
                                   FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> FStar_Pervasives_Native.Some q) quals1 in
                      ((let uu___122_6480 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___122_6480.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___122_6480.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___122_6480.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6489 -> failwith "impossible" in
                (match uu____6361 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6538 = log env2 in
                       if uu____6538
                       then
                         let uu____6539 =
                           let uu____6540 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6555 =
                                         let uu____6564 =
                                           let uu____6565 =
                                             let uu____6568 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6568.FStar_Syntax_Syntax.fv_name in
                                           uu____6565.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6564 in
                                       match uu____6555 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6575 -> false in
                                     if should_log
                                     then
                                       let uu____6584 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6585 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6584 uu____6585
                                     else "")) in
                           FStar_All.pipe_right uu____6540
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6539
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6616 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6616 with
                              | (bs1,c1) ->
                                  let uu____6623 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6623
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6635 =
                                            let uu____6636 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6636.FStar_Syntax_Syntax.n in
                                          (match uu____6635 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6661 =
                                                 let uu____6662 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6662.FStar_Syntax_Syntax.n in
                                               (match uu____6661 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6672 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6672 in
                                                    let uu____6673 =
                                                      let uu____6674 =
                                                        let uu____6675 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6675 args in
                                                      uu____6674
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6673 u
                                                | uu____6678 -> c1)
                                           | uu____6679 -> c1)
                                      | uu____6680 -> c1 in
                                    let uu___123_6681 = t1 in
                                    let uu____6682 =
                                      let uu____6683 =
                                        let uu____6696 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6696) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6683 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6682;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___123_6681.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___123_6681.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6720 =
                               let uu____6721 = FStar_Syntax_Subst.compress h in
                               uu____6721.FStar_Syntax_Syntax.n in
                             (match uu____6720 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6731 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6731 in
                                  let uu____6732 =
                                    let uu____6733 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6733
                                      args in
                                  uu____6732 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6736 -> t1)
                         | uu____6737 -> t1 in
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
                           let uu____6765 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6765 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6782 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6782, (FStar_Pervasives_Native.snd x)))
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
                           let uu____6813 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6813 in
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
                         let uu___124_6820 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___125_6832 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6832.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6832.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6832.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6832.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___124_6820.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___124_6820.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___124_6820.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___124_6820.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6849 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6849 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6883 =
                                    let uu____6884 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6884.FStar_Syntax_Syntax.n in
                                  (match uu____6883 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6917 =
                                           let uu____6920 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6920.FStar_Syntax_Syntax.fv_name in
                                         uu____6917.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6922 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6922 in
                                       let uu____6923 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____6923 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____6933 =
                                              let uu____6934 =
                                                let uu____6935 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____6935 in
                                              Prims.op_Negation uu____6934 in
                                            if uu____6933
                                            then
                                              ((let uu____6965 =
                                                  let uu____6966 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____6966 in
                                                if uu____6965
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
                                               (let uu____7009 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid in
                                                if uu____7009
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
                                   | uu____7038 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7043 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7065 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7065
                             then
                               let uu____7066 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7067 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7066 uu____7067
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
             (fun uu___92_7120  ->
                match uu___92_7120 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7121 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7127) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7133 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7142 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7147 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____7172 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7196) ->
          let uu____7205 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7205
          then
            let for_export_bundle se1 uu____7236 =
              match uu____7236 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7275,uu____7276) ->
                       let dec =
                         let uu___126_7286 = se1 in
                         let uu____7287 =
                           let uu____7288 =
                             let uu____7295 =
                               let uu____7298 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7298 in
                             (l, us, uu____7295) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7288 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7287;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___126_7286.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___126_7286.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___126_7286.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7310,uu____7311,uu____7312) ->
                       let dec =
                         let uu___127_7318 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___127_7318.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___127_7318.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___127_7318.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7323 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7345,uu____7346,uu____7347) ->
          let uu____7348 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7348 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7369 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7369
          then
            ([(let uu___128_7385 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___128_7385.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___128_7385.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___128_7385.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7387 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___93_7391  ->
                       match uu___93_7391 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7392 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7397 -> true
                       | uu____7398 -> false)) in
             if uu____7387 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7416 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7421 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7426 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7431 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7436 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7454) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7471 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7471
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
          let uu____7502 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7502
          then
            let uu____7511 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___129_7524 = se in
                      let uu____7525 =
                        let uu____7526 =
                          let uu____7533 =
                            let uu____7534 =
                              let uu____7537 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7537.FStar_Syntax_Syntax.fv_name in
                            uu____7534.FStar_Syntax_Syntax.v in
                          (uu____7533, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7526 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7525;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___129_7524.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___129_7524.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___129_7524.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7511, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7559 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7576 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____7592 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____7596 = FStar_Options.using_facts_from () in
                 match uu____7596 with
                 | FStar_Pervasives_Native.Some ns ->
                     let proof_ns =
                       let uu____7617 =
                         let uu____7626 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____7626 [([], false)] in
                       [uu____7617] in
                     let uu___130_7681 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___130_7681.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___130_7681.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___130_7681.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___130_7681.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___130_7681.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___130_7681.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___130_7681.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___130_7681.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___130_7681.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___130_7681.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___130_7681.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___130_7681.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___130_7681.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___130_7681.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___130_7681.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___130_7681.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___130_7681.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___130_7681.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___130_7681.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___130_7681.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___130_7681.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.type_of =
                         (uu___130_7681.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___130_7681.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___130_7681.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___130_7681.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___130_7681.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___130_7681.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___130_7681.FStar_TypeChecker_Env.identifier_info)
                     }
                 | FStar_Pervasives_Native.None  -> env))
           | uu____7684 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7685 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7695 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7695) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7696,uu____7697,uu____7698) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7702  ->
                  match uu___94_7702 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7703 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7704,uu____7705) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_7713  ->
                  match uu___94_7713 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7714 -> false))
          -> env
      | uu____7715 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7777 se =
        match uu____7777 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7830 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7830
              then
                let uu____7831 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7831
              else ());
             (let uu____7833 = tc_decl env1 se in
              match uu____7833 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7883 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7883
                             then
                               let uu____7884 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7884
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
                    (let uu____7907 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7907
                     then
                       let uu____7908 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7914 =
                                  let uu____7915 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7915 "\n" in
                                Prims.strcat s uu____7914) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7908
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7920 =
                       let accum_exports_hidden uu____7950 se1 =
                         match uu____7950 with
                         | (exports1,hidden1) ->
                             let uu____7978 = for_export hidden1 se1 in
                             (match uu____7978 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7920 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___131_8057 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___131_8057.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___131_8057.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___131_8057.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___131_8057.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8135 = acc in
        match uu____8135 with
        | (uu____8170,uu____8171,env1,uu____8173) ->
            let uu____8186 =
              FStar_Util.record_time
                (fun uu____8232  -> process_one_decl acc se) in
            (match uu____8186 with
             | (r,ms_elapsed) ->
                 ((let uu____8296 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8296
                   then
                     let uu____8297 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8298 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8297 uu____8298
                   else ());
                  r)) in
      let uu____8300 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8300 with
      | (ses1,exports,env1,uu____8348) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____8387 = FStar_Options.debug_any () in
       if uu____8387
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
         let uu___132_8393 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___132_8393.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___132_8393.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___132_8393.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___132_8393.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___132_8393.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___132_8393.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___132_8393.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___132_8393.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___132_8393.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___132_8393.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___132_8393.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___132_8393.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___132_8393.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___132_8393.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___132_8393.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___132_8393.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___132_8393.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___132_8393.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___132_8393.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___132_8393.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___132_8393.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___132_8393.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___132_8393.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___132_8393.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___132_8393.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___132_8393.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___132_8393.FStar_TypeChecker_Env.identifier_info)
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
        let uu____8396 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____8396 with
        | (ses,exports,env3) ->
            ((let uu___133_8429 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___133_8429.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___133_8429.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___133_8429.FStar_Syntax_Syntax.is_interface)
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
        let uu____8454 = tc_decls env decls in
        match uu____8454 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___134_8485 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___134_8485.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___134_8485.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___134_8485.FStar_Syntax_Syntax.is_interface)
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
          let uu___135_8505 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___135_8505.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___135_8505.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___135_8505.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___135_8505.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___135_8505.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___135_8505.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___135_8505.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___135_8505.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___135_8505.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___135_8505.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___135_8505.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___135_8505.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___135_8505.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___135_8505.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___135_8505.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___135_8505.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___135_8505.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___135_8505.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.type_of =
              (uu___135_8505.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___135_8505.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___135_8505.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___135_8505.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___135_8505.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___135_8505.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___135_8505.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___135_8505.FStar_TypeChecker_Env.identifier_info)
          } in
        let check_term lid univs1 t =
          let uu____8516 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8516 with
          | (univs2,t1) ->
              ((let uu____8524 =
                  let uu____8525 =
                    let uu____8528 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8528 in
                  FStar_All.pipe_left uu____8525
                    (FStar_Options.Other "Exports") in
                if uu____8524
                then
                  let uu____8529 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8530 =
                    let uu____8531 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8531
                      (FStar_String.concat ", ") in
                  let uu____8540 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8529 uu____8530 uu____8540
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8543 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8543 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____8567 =
             let uu____8568 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8569 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8568 uu____8569 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8567);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8576) ->
              let uu____8585 =
                let uu____8586 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8586 in
              if uu____8585
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8596,uu____8597) ->
              let t =
                let uu____8609 =
                  let uu____8612 =
                    let uu____8613 =
                      let uu____8626 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8626) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8613 in
                  FStar_Syntax_Syntax.mk uu____8612 in
                uu____8609 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8633,uu____8634,uu____8635) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8643 =
                let uu____8644 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8644 in
              if uu____8643 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8648,lbs),uu____8650) ->
              let uu____8665 =
                let uu____8666 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8666 in
              if uu____8665
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags) ->
              let uu____8685 =
                let uu____8686 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8686 in
              if uu____8685
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8693 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8694 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8701 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8702 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8703 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8704 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
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
          let uu___136_8723 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___136_8723.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___136_8723.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
        (let uu____8726 =
           let uu____8727 = FStar_Options.lax () in
           Prims.op_Negation uu____8727 in
         if uu____8726 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____8733 =
           let uu____8734 = FStar_Options.interactive () in
           Prims.op_Negation uu____8734 in
         if uu____8733
         then
           let uu____8735 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____8735 FStar_Pervasives.ignore
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
      let uu____8749 = tc_partial_modul env modul in
      match uu____8749 with
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
      (let uu____8782 = FStar_Options.debug_any () in
       if uu____8782
       then
         let uu____8783 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8783
       else ());
      (let env1 =
         let uu___137_8787 = env in
         let uu____8788 =
           let uu____8789 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8789 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___137_8787.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___137_8787.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___137_8787.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___137_8787.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___137_8787.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___137_8787.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___137_8787.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___137_8787.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___137_8787.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___137_8787.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___137_8787.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___137_8787.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___137_8787.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___137_8787.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___137_8787.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___137_8787.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___137_8787.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___137_8787.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8788;
           FStar_TypeChecker_Env.lax_universes =
             (uu___137_8787.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___137_8787.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___137_8787.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___137_8787.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___137_8787.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___137_8787.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___137_8787.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___137_8787.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___137_8787.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___137_8787.FStar_TypeChecker_Env.identifier_info)
         } in
       let uu____8790 = tc_modul env1 m in
       match uu____8790 with
       | (m1,env2) ->
           ((let uu____8802 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8802
             then
               let uu____8803 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8803
             else ());
            (let uu____8806 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8806
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
                       let uu____8837 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8837 with
                       | (univnames1,e) ->
                           let uu___138_8844 = lb in
                           let uu____8845 =
                             let uu____8848 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8848 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___138_8844.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___138_8844.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___138_8844.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___138_8844.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8845
                           } in
                     let uu___139_8849 = se in
                     let uu____8850 =
                       let uu____8851 =
                         let uu____8858 =
                           let uu____8865 = FStar_List.map update lbs in
                           (b, uu____8865) in
                         (uu____8858, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8851 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8850;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___139_8849.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___139_8849.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___139_8849.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___139_8849.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8878 -> se in
               let normalized_module =
                 let uu___140_8880 = m1 in
                 let uu____8881 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___140_8880.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8881;
                   FStar_Syntax_Syntax.exports =
                     (uu___140_8880.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___140_8880.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8882 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8882
             else ());
            (m1, env2)))