open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | Some l ->
          let lid =
            let uu____11 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____11 l in
          let uu___83_12 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___83_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___83_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___83_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___83_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___83_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___83_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___83_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___83_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___83_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___83_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___83_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___83_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___83_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___83_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___83_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___83_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___83_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___83_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___83_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___83_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___83_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___83_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___83_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____18 = FStar_TypeChecker_Env.current_module env in
                let uu____19 =
                  let uu____20 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____20 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____18 uu____19
            | l::uu____22 -> l in
          let uu___84_24 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___84_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___84_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___84_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___84_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___84_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___84_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___84_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___84_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___84_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___84_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___84_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___84_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___84_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___84_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___84_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___84_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___84_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___84_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___84_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___84_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___84_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___84_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___84_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____30 =
         let uu____31 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31 in
       Prims.op_Negation uu____30)
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____41 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____41 with
        | (t,c,g) ->
            (FStar_ST.write t.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____63 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         match uu____63 with
         | true  ->
             let uu____64 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2
               "Term has been %s-transformed to:\n%s\n----------\n" s
               uu____64
         | uu____65 -> ());
        (let uu____66 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____66 with
         | (t',uu____71,uu____72) ->
             ((let uu____74 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               match uu____74 with
               | true  ->
                   let uu____75 = FStar_Syntax_Print.term_to_string t' in
                   FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                     uu____75
               | uu____76 -> ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____86 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____86
let check_nogen env t k =
  let t = tc_check_trivial_guard env t k in
  let uu____108 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t in
  ([], uu____108)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____130 =
          let uu____131 =
            let uu____132 =
              let uu____135 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____135, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____132 in
          Prims.raise uu____131 in
        let s = FStar_Syntax_Subst.compress s in
        match s.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs = FStar_Syntax_Subst.open_binders bs in
            (match bs with
             | (a,uu____163)::(wp,uu____165)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____174 -> fail ())
        | uu____175 -> fail ()
let open_univ_vars:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
          FStar_Syntax_Syntax.aqual) Prims.list* FStar_Syntax_Syntax.comp)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____205 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____205 with | (uvs,c) -> (uvs, [], c))
        | uu____221 ->
            let t' = FStar_Syntax_Util.arrow binders c in
            let uu____228 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____228 with
             | (uvs,t') ->
                 let uu____239 =
                   let uu____240 = FStar_Syntax_Subst.compress t' in
                   uu____240.FStar_Syntax_Syntax.n in
                 (match uu____239 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                      (uvs, binders, c)
                  | uu____266 -> failwith "Impossible"))
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____335 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____335 with
      | (effect_params_un,signature_un,opening) ->
          let uu____342 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____342 with
           | (effect_params,env,uu____348) ->
               let uu____349 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____349 with
                | (signature,uu____353) ->
                    let ed =
                      let uu___85_355 = ed in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___85_355.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___85_355.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___85_355.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___85_355.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___85_355.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___85_355.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___85_355.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___85_355.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___85_355.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___85_355.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___85_355.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___85_355.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___85_355.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___85_355.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___85_355.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___85_355.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___85_355.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___85_355.FStar_Syntax_Syntax.actions)
                      } in
                    let ed =
                      match effect_params with
                      | [] -> ed
                      | uu____359 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___86_377 = ed in
                          let uu____378 = op ed.FStar_Syntax_Syntax.ret_wp in
                          let uu____379 = op ed.FStar_Syntax_Syntax.bind_wp in
                          let uu____380 =
                            op ed.FStar_Syntax_Syntax.if_then_else in
                          let uu____381 = op ed.FStar_Syntax_Syntax.ite_wp in
                          let uu____382 = op ed.FStar_Syntax_Syntax.stronger in
                          let uu____383 = op ed.FStar_Syntax_Syntax.close_wp in
                          let uu____384 = op ed.FStar_Syntax_Syntax.assert_p in
                          let uu____385 = op ed.FStar_Syntax_Syntax.assume_p in
                          let uu____386 = op ed.FStar_Syntax_Syntax.null_wp in
                          let uu____387 = op ed.FStar_Syntax_Syntax.trivial in
                          let uu____388 =
                            let uu____389 =
                              op ([], (ed.FStar_Syntax_Syntax.repr)) in
                            Prims.snd uu____389 in
                          let uu____395 =
                            op ed.FStar_Syntax_Syntax.return_repr in
                          let uu____396 = op ed.FStar_Syntax_Syntax.bind_repr in
                          let uu____397 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___87_400 = a in
                                 let uu____401 =
                                   let uu____402 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   Prims.snd uu____402 in
                                 let uu____408 =
                                   let uu____409 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   Prims.snd uu____409 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___87_400.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___87_400.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___87_400.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____401;
                                   FStar_Syntax_Syntax.action_typ = uu____408
                                 }) ed.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___86_377.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___86_377.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___86_377.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___86_377.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___86_377.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___86_377.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____378;
                            FStar_Syntax_Syntax.bind_wp = uu____379;
                            FStar_Syntax_Syntax.if_then_else = uu____380;
                            FStar_Syntax_Syntax.ite_wp = uu____381;
                            FStar_Syntax_Syntax.stronger = uu____382;
                            FStar_Syntax_Syntax.close_wp = uu____383;
                            FStar_Syntax_Syntax.assert_p = uu____384;
                            FStar_Syntax_Syntax.assume_p = uu____385;
                            FStar_Syntax_Syntax.null_wp = uu____386;
                            FStar_Syntax_Syntax.trivial = uu____387;
                            FStar_Syntax_Syntax.repr = uu____388;
                            FStar_Syntax_Syntax.return_repr = uu____395;
                            FStar_Syntax_Syntax.bind_repr = uu____396;
                            FStar_Syntax_Syntax.actions = uu____397
                          } in
                    let wp_with_fresh_result_type env mname signature =
                      let fail t =
                        let uu____437 =
                          let uu____438 =
                            let uu____441 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env mname t in
                            (uu____441, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____438 in
                        Prims.raise uu____437 in
                      let uu____446 =
                        let uu____447 = FStar_Syntax_Subst.compress signature in
                        uu____447.FStar_Syntax_Syntax.n in
                      match uu____446 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs = FStar_Syntax_Subst.open_binders bs in
                          (match bs with
                           | (a,uu____472)::(wp,uu____474)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____483 -> fail signature)
                      | uu____484 -> fail signature in
                    let uu____485 =
                      wp_with_fresh_result_type env
                        ed.FStar_Syntax_Syntax.mname
                        ed.FStar_Syntax_Syntax.signature in
                    (match uu____485 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____503 =
                           let uu____504 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____504 with
                           | (signature,uu____512) ->
                               wp_with_fresh_result_type env
                                 ed.FStar_Syntax_Syntax.mname signature in
                         let env =
                           let uu____514 =
                             FStar_Syntax_Syntax.new_bv None
                               ed.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____514 in
                         ((let uu____516 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           match uu____516 with
                           | true  ->
                               let uu____517 =
                                 FStar_Syntax_Print.lid_to_string
                                   ed.FStar_Syntax_Syntax.mname in
                               let uu____518 =
                                 FStar_Syntax_Print.binders_to_string " "
                                   ed.FStar_Syntax_Syntax.binders in
                               let uu____519 =
                                 FStar_Syntax_Print.term_to_string
                                   ed.FStar_Syntax_Syntax.signature in
                               let uu____520 =
                                 let uu____521 =
                                   FStar_Syntax_Syntax.bv_to_name a in
                                 FStar_Syntax_Print.term_to_string uu____521 in
                               let uu____522 =
                                 FStar_Syntax_Print.term_to_string
                                   a.FStar_Syntax_Syntax.sort in
                               FStar_Util.print5
                                 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                 uu____517 uu____518 uu____519 uu____520
                                 uu____522
                           | uu____523 -> ());
                          (let check_and_gen' env uu____535 k =
                             match uu____535 with
                             | (uu____540,t) -> check_and_gen env t k in
                           let return_wp =
                             let expected_k =
                               let uu____548 =
                                 let uu____552 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____553 =
                                   let uu____555 =
                                     let uu____556 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____556 in
                                   [uu____555] in
                                 uu____552 :: uu____553 in
                               let uu____557 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____548 uu____557 in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp
                               expected_k in
                           let bind_wp =
                             let uu____561 = fresh_effect_signature () in
                             match uu____561 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____575 =
                                     let uu____579 =
                                       let uu____580 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____580 in
                                     [uu____579] in
                                   let uu____581 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____575
                                     uu____581 in
                                 let expected_k =
                                   let uu____587 =
                                     let uu____591 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____592 =
                                       let uu____594 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____595 =
                                         let uu____597 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____598 =
                                           let uu____600 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____601 =
                                             let uu____603 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____603] in
                                           uu____600 :: uu____601 in
                                         uu____597 :: uu____598 in
                                       uu____594 :: uu____595 in
                                     uu____591 :: uu____592 in
                                   let uu____604 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____587
                                     uu____604 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else =
                             let p =
                               let uu____609 =
                                 let uu____610 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____610 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname))
                                 uu____609 in
                             let expected_k =
                               let uu____618 =
                                 let uu____622 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____623 =
                                   let uu____625 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____626 =
                                     let uu____628 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____629 =
                                       let uu____631 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____631] in
                                     uu____628 :: uu____629 in
                                   uu____625 :: uu____626 in
                                 uu____622 :: uu____623 in
                               let uu____632 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____618 uu____632 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.if_then_else expected_k in
                           let ite_wp =
                             let expected_k =
                               let uu____639 =
                                 let uu____643 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____644 =
                                   let uu____646 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____646] in
                                 uu____643 :: uu____644 in
                               let uu____647 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____639 uu____647 in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp
                               expected_k in
                           let stronger =
                             let uu____651 = FStar_Syntax_Util.type_u () in
                             match uu____651 with
                             | (t,uu____655) ->
                                 let expected_k =
                                   let uu____659 =
                                     let uu____663 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____664 =
                                       let uu____666 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____667 =
                                         let uu____669 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____669] in
                                       uu____666 :: uu____667 in
                                     uu____663 :: uu____664 in
                                   let uu____670 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____659
                                     uu____670 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.stronger expected_k in
                           let close_wp =
                             let b =
                               let uu____675 =
                                 let uu____676 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____676 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname))
                                 uu____675 in
                             let b_wp_a =
                               let uu____684 =
                                 let uu____688 =
                                   let uu____689 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____689 in
                                 [uu____688] in
                               let uu____690 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____684 uu____690 in
                             let expected_k =
                               let uu____696 =
                                 let uu____700 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____701 =
                                   let uu____703 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____704 =
                                     let uu____706 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____706] in
                                   uu____703 :: uu____704 in
                                 uu____700 :: uu____701 in
                               let uu____707 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____696 uu____707 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let uu____714 =
                                 let uu____718 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____719 =
                                   let uu____721 =
                                     let uu____722 =
                                       let uu____723 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____723
                                         Prims.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____722 in
                                   let uu____728 =
                                     let uu____730 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____730] in
                                   uu____721 :: uu____728 in
                                 uu____718 :: uu____719 in
                               let uu____731 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____714 uu____731 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let uu____738 =
                                 let uu____742 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____743 =
                                   let uu____745 =
                                     let uu____746 =
                                       let uu____747 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____747
                                         Prims.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____746 in
                                   let uu____752 =
                                     let uu____754 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____754] in
                                   uu____745 :: uu____752 in
                                 uu____742 :: uu____743 in
                               let uu____755 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____738 uu____755 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let uu____762 =
                                 let uu____766 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____766] in
                               let uu____767 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____762 uu____767 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____771 = FStar_Syntax_Util.type_u () in
                             match uu____771 with
                             | (t,uu____775) ->
                                 let expected_k =
                                   let uu____779 =
                                     let uu____783 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____784 =
                                       let uu____786 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____786] in
                                     uu____783 :: uu____784 in
                                   let uu____787 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____779
                                     uu____787 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____790 =
                             let uu____796 =
                               let uu____797 =
                                 FStar_Syntax_Subst.compress
                                   ed.FStar_Syntax_Syntax.repr in
                               uu____797.FStar_Syntax_Syntax.n in
                             match uu____796 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed.FStar_Syntax_Syntax.repr),
                                   (ed.FStar_Syntax_Syntax.bind_repr),
                                   (ed.FStar_Syntax_Syntax.return_repr),
                                   (ed.FStar_Syntax_Syntax.actions))
                             | uu____806 ->
                                 let repr =
                                   let uu____808 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____808 with
                                   | (t,uu____812) ->
                                       let expected_k =
                                         let uu____816 =
                                           let uu____820 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____821 =
                                             let uu____823 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____823] in
                                           uu____820 :: uu____821 in
                                         let uu____824 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____816
                                           uu____824 in
                                       tc_check_trivial_guard env
                                         ed.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env repr in
                                   let uu____837 =
                                     let uu____840 =
                                       let uu____841 =
                                         let uu____851 =
                                           let uu____853 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____854 =
                                             let uu____856 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____856] in
                                           uu____853 :: uu____854 in
                                         (repr, uu____851) in
                                       FStar_Syntax_Syntax.Tm_app uu____841 in
                                     FStar_Syntax_Syntax.mk uu____840 in
                                   uu____837 None FStar_Range.dummyRange in
                                 let mk_repr a wp =
                                   let uu____875 =
                                     FStar_Syntax_Syntax.bv_to_name a in
                                   mk_repr' uu____875 wp in
                                 let destruct_repr t =
                                   let uu____886 =
                                     let uu____887 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____887.FStar_Syntax_Syntax.n in
                                   match uu____886 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____896,(t,uu____898)::(wp,uu____900)::[])
                                       -> (t, wp)
                                   | uu____934 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____943 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right uu____943
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____944 = fresh_effect_signature () in
                                   match uu____944 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____958 =
                                           let uu____962 =
                                             let uu____963 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____963 in
                                           [uu____962] in
                                         let uu____964 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____958
                                           uu____964 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let uu____970 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____970 in
                                       let wp_g_x =
                                         let uu____974 =
                                           let uu____975 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____976 =
                                             let uu____977 =
                                               let uu____978 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____978 in
                                             [uu____977] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____975 uu____976 in
                                         uu____974 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____989 =
                                             let uu____990 =
                                               let uu____991 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____991
                                                 Prims.snd in
                                             let uu____996 =
                                               let uu____997 =
                                                 let uu____999 =
                                                   let uu____1001 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____1002 =
                                                     let uu____1004 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____1005 =
                                                       let uu____1007 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____1008 =
                                                         let uu____1010 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____1010] in
                                                       uu____1007 ::
                                                         uu____1008 in
                                                     uu____1004 :: uu____1005 in
                                                   uu____1001 :: uu____1002 in
                                                 r :: uu____999 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____997 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____990 uu____996 in
                                           uu____989 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____1018 =
                                           let uu____1022 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____1023 =
                                             let uu____1025 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____1026 =
                                               let uu____1028 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____1029 =
                                                 let uu____1031 =
                                                   let uu____1032 =
                                                     let uu____1033 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____1033 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1032 in
                                                 let uu____1034 =
                                                   let uu____1036 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____1037 =
                                                     let uu____1039 =
                                                       let uu____1040 =
                                                         let uu____1041 =
                                                           let uu____1045 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____1045] in
                                                         let uu____1046 =
                                                           let uu____1049 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1049 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1041
                                                           uu____1046 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1040 in
                                                     [uu____1039] in
                                                   uu____1036 :: uu____1037 in
                                                 uu____1031 :: uu____1034 in
                                               uu____1028 :: uu____1029 in
                                             uu____1025 :: uu____1026 in
                                           uu____1022 :: uu____1023 in
                                         let uu____1050 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____1018
                                           uu____1050 in
                                       let uu____1053 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env expected_k in
                                       (match uu____1053 with
                                        | (expected_k,uu____1058,uu____1059)
                                            ->
                                            let env =
                                              FStar_TypeChecker_Env.set_range
                                                env
                                                (Prims.snd
                                                   ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env =
                                              let uu___88_1063 = env in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___88_1063.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___88_1063.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___88_1063.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___88_1063.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env
                                                ed.FStar_Syntax_Syntax.bind_repr
                                                expected_k in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let uu____1070 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1070 in
                                   let res =
                                     let wp =
                                       let uu____1077 =
                                         let uu____1078 =
                                           let uu____1079 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1079
                                             Prims.snd in
                                         let uu____1084 =
                                           let uu____1085 =
                                             let uu____1087 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1088 =
                                               let uu____1090 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1090] in
                                             uu____1087 :: uu____1088 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1085 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1078 uu____1084 in
                                       uu____1077 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1098 =
                                       let uu____1102 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1103 =
                                         let uu____1105 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1105] in
                                       uu____1102 :: uu____1103 in
                                     let uu____1106 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1098
                                       uu____1106 in
                                   let uu____1109 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env expected_k in
                                   match uu____1109 with
                                   | (expected_k,uu____1117,uu____1118) ->
                                       let env =
                                         FStar_TypeChecker_Env.set_range env
                                           (Prims.snd
                                              ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____1121 =
                                         check_and_gen' env
                                           ed.FStar_Syntax_Syntax.return_repr
                                           expected_k in
                                       (match uu____1121 with
                                        | (univs,repr) ->
                                            (match univs with
                                             | [] -> ([], repr)
                                             | uu____1133 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____1144 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1144 with
                                     | (act_typ,uu____1149,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env act_typ in
                                         ((let uu____1153 =
                                             FStar_TypeChecker_Env.debug env
                                               (FStar_Options.Other "ED") in
                                           match uu____1153 with
                                           | true  ->
                                               let uu____1154 =
                                                 FStar_Syntax_Print.term_to_string
                                                   act.FStar_Syntax_Syntax.action_defn in
                                               let uu____1155 =
                                                 FStar_Syntax_Print.term_to_string
                                                   act_typ in
                                               FStar_Util.print3
                                                 "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                 (FStar_Ident.text_of_lid
                                                    act.FStar_Syntax_Syntax.action_name)
                                                 uu____1154 uu____1155
                                           | uu____1156 -> ());
                                          (let uu____1157 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1157 with
                                           | (act_defn,uu____1162,g_a) ->
                                               let act_defn =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env act_defn in
                                               let act_typ =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env act_typ in
                                               let uu____1166 =
                                                 let act_typ =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ in
                                                 match act_typ.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1184 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1184 with
                                                      | (bs,uu____1190) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let uu____1197 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs uu____1197 in
                                                          let uu____1200 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env k in
                                                          (match uu____1200
                                                           with
                                                           | (k,uu____1207,g)
                                                               -> (k, g)))
                                                 | uu____1209 ->
                                                     let uu____1210 =
                                                       let uu____1211 =
                                                         let uu____1214 =
                                                           let uu____1215 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ in
                                                           let uu____1216 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1215
                                                             uu____1216 in
                                                         (uu____1214,
                                                           (act_defn.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1211 in
                                                     Prims.raise uu____1210 in
                                               (match uu____1166 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env act_typ
                                                        expected_k in
                                                    ((let uu____1223 =
                                                        let uu____1224 =
                                                          let uu____1225 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1225 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1224 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env uu____1223);
                                                     (let act_typ =
                                                        let uu____1229 =
                                                          let uu____1230 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1230.FStar_Syntax_Syntax.n in
                                                        match uu____1229 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1247 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1247
                                                             with
                                                             | (bs,c) ->
                                                                 let uu____1254
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c) in
                                                                 (match uu____1254
                                                                  with
                                                                  | (a,wp) ->
                                                                    let c =
                                                                    let uu____1274
                                                                    =
                                                                    let uu____1275
                                                                    =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env a in
                                                                    [uu____1275] in
                                                                    let uu____1276
                                                                    =
                                                                    let uu____1282
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1282] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1274;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1276;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1283
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs
                                                                    uu____1283))
                                                        | uu____1286 ->
                                                            failwith "" in
                                                      let uu____1289 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env act_defn in
                                                      match uu____1289 with
                                                      | (univs,act_defn) ->
                                                          let act_typ =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env act_typ in
                                                          let uu___89_1295 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___89_1295.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___89_1295.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs;
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____790 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1311 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed.FStar_Syntax_Syntax.binders uu____1311 in
                               let uu____1314 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1314 with
                                | (univs,t) ->
                                    let signature =
                                      let uu____1320 =
                                        let uu____1323 =
                                          let uu____1324 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1324.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1323) in
                                      match uu____1320 with
                                      | ([],uu____1327) -> t
                                      | (uu____1333,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1334,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1346 -> failwith "Impossible" in
                                    let close n ts =
                                      let ts =
                                        let uu____1357 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs uu____1357 in
                                      let m =
                                        FStar_List.length (Prims.fst ts) in
                                      (let uu____1362 =
                                         ((n >= (Prims.parse_int "0")) &&
                                            (let uu____1363 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts) in
                                             Prims.op_Negation uu____1363))
                                           && (m <> n) in
                                       match uu____1362 with
                                       | true  ->
                                           let error =
                                             match m < n with
                                             | true  ->
                                                 "not universe-polymorphic enough"
                                             | uu____1371 ->
                                                 "too universe-polymorphic" in
                                           let uu____1372 =
                                             let uu____1373 =
                                               FStar_Util.string_of_int n in
                                             let uu____1374 =
                                               FStar_Syntax_Print.tscheme_to_string
                                                 ts in
                                             FStar_Util.format3
                                               "The effect combinator is %s (n=%s) (%s)"
                                               error uu____1373 uu____1374 in
                                           failwith uu____1372
                                       | uu____1375 -> ());
                                      ts in
                                    let close_action act =
                                      let uu____1380 =
                                        close (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1380 with
                                      | (univs,defn) ->
                                          let uu____1385 =
                                            close (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1385 with
                                           | (univs',typ) ->
                                               let uu___90_1391 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___90_1391.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___90_1391.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let nunivs = FStar_List.length univs in
                                    let ed =
                                      let uu___91_1396 = ed in
                                      let uu____1397 =
                                        close (Prims.parse_int "0") return_wp in
                                      let uu____1398 =
                                        close (Prims.parse_int "1") bind_wp in
                                      let uu____1399 =
                                        close (Prims.parse_int "0")
                                          if_then_else in
                                      let uu____1400 =
                                        close (Prims.parse_int "0") ite_wp in
                                      let uu____1401 =
                                        close (Prims.parse_int "0") stronger in
                                      let uu____1402 =
                                        close (Prims.parse_int "1") close_wp in
                                      let uu____1403 =
                                        close (Prims.parse_int "0") assert_p in
                                      let uu____1404 =
                                        close (Prims.parse_int "0") assume_p in
                                      let uu____1405 =
                                        close (Prims.parse_int "0") null_wp in
                                      let uu____1406 =
                                        close (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1407 =
                                        let uu____1408 =
                                          close (Prims.parse_int "0")
                                            ([], repr) in
                                        Prims.snd uu____1408 in
                                      let uu____1414 =
                                        close (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1415 =
                                        close (Prims.parse_int "1") bind_repr in
                                      let uu____1416 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___91_1396.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___91_1396.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___91_1396.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1397;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1398;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1399;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1400;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1401;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1402;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1403;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1404;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1405;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1406;
                                        FStar_Syntax_Syntax.repr = uu____1407;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1414;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1415;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1416
                                      } in
                                    ((let uu____1419 =
                                        (FStar_TypeChecker_Env.debug env
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other "ED")) in
                                      match uu____1419 with
                                      | true  ->
                                          let uu____1420 =
                                            FStar_Syntax_Print.eff_decl_to_string
                                              false ed in
                                          FStar_Util.print_string uu____1420
                                      | uu____1421 -> ());
                                     ed)))))))
and cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt Prims.option)
  =
  fun env  ->
    fun ed  ->
      let uu____1424 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1424 with
      | (effect_binders_un,signature_un) ->
          let uu____1434 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1434 with
           | (effect_binders,env,uu____1445) ->
               let uu____1446 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____1446 with
                | (signature,uu____1455) ->
                    let effect_binders =
                      FStar_List.map
                        (fun uu____1464  ->
                           match uu____1464 with
                           | (bv,qual) ->
                               let uu____1471 =
                                 let uu___92_1472 = bv in
                                 let uu____1473 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___92_1472.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___92_1472.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1473
                                 } in
                               (uu____1471, qual)) effect_binders in
                    let uu____1476 =
                      let uu____1481 =
                        let uu____1482 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1482.FStar_Syntax_Syntax.n in
                      match uu____1481 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1490)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1505 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1476 with
                     | (a,effect_marker) ->
                         let a =
                           let uu____1522 = FStar_Syntax_Syntax.is_null_bv a in
                           match uu____1522 with
                           | true  ->
                               let uu____1523 =
                                 let uu____1525 =
                                   FStar_Syntax_Syntax.range_of_bv a in
                                 Some uu____1525 in
                               FStar_Syntax_Syntax.gen_bv "a" uu____1523
                                 a.FStar_Syntax_Syntax.sort
                           | uu____1526 -> a in
                         let open_and_check t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders in
                           let t = FStar_Syntax_Subst.subst subst t in
                           let uu____1535 =
                             FStar_TypeChecker_TcTerm.tc_term env t in
                           match uu____1535 with
                           | (t,comp,uu____1543) -> (t, comp) in
                         let mk x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1554 =
                           open_and_check ed.FStar_Syntax_Syntax.repr in
                         (match uu____1554 with
                          | (repr,_comp) ->
                              ((let uu____1565 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "ED") in
                                match uu____1565 with
                                | true  ->
                                    let uu____1566 =
                                      FStar_Syntax_Print.term_to_string repr in
                                    FStar_Util.print1
                                      "Representation is: %s\n" uu____1566
                                | uu____1567 -> ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type = recheck_debug "*" env wp_type in
                                let wp_a =
                                  let uu____1572 =
                                    let uu____1573 =
                                      let uu____1574 =
                                        let uu____1584 =
                                          let uu____1588 =
                                            let uu____1591 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            let uu____1592 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1591, uu____1592) in
                                          [uu____1588] in
                                        (wp_type, uu____1584) in
                                      FStar_Syntax_Syntax.Tm_app uu____1574 in
                                    mk uu____1573 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env
                                    uu____1572 in
                                let effect_signature =
                                  let binders =
                                    let uu____1607 =
                                      let uu____1610 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a, uu____1610) in
                                    let uu____1611 =
                                      let uu____1615 =
                                        let uu____1616 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1616
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1615] in
                                    uu____1607 :: uu____1611 in
                                  let binders =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders, effect_marker)) in
                                let effect_signature =
                                  recheck_debug
                                    "turned into the effect signature" env
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       (Prims.strcat
                                          (FStar_Ident.text_of_lid
                                             ed.FStar_Syntax_Syntax.mname)
                                          (Prims.strcat "_" name)))
                                    FStar_Range.dummyRange in
                                let elaborate_and_star dmff_env item =
                                  let uu____1649 = item in
                                  match uu____1649 with
                                  | (u_item,item) ->
                                      let uu____1661 = open_and_check item in
                                      (match uu____1661 with
                                       | (item,item_comp) ->
                                           ((let uu____1671 =
                                               let uu____1672 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1672 in
                                             match uu____1671 with
                                             | true  ->
                                                 let uu____1673 =
                                                   let uu____1674 =
                                                     let uu____1675 =
                                                       FStar_Syntax_Print.term_to_string
                                                         item in
                                                     let uu____1676 =
                                                       FStar_Syntax_Print.lcomp_to_string
                                                         item_comp in
                                                     FStar_Util.format2
                                                       "Computation for [%s] is not total : %s !"
                                                       uu____1675 uu____1676 in
                                                   FStar_Errors.Err
                                                     uu____1674 in
                                                 Prims.raise uu____1673
                                             | uu____1677 -> ());
                                            (let uu____1678 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env item in
                                             match uu____1678 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp =
                                                   recheck_debug "*" env
                                                     item_wp in
                                                 let item_elab =
                                                   recheck_debug "_" env
                                                     item_elab in
                                                 (dmff_env, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____1691 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1691 with
                                | (dmff_env,uu____1702,bind_wp,bind_elab) ->
                                    let uu____1705 =
                                      elaborate_and_star dmff_env
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1705 with
                                     | (dmff_env,uu____1716,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1720 =
                                             let uu____1721 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1721.FStar_Syntax_Syntax.n in
                                           match uu____1720 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1759 =
                                                 let uu____1767 =
                                                   let uu____1770 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1770 in
                                                 match uu____1767 with
                                                 | (b1::b2::[],body) ->
                                                     (b1, b2, body)
                                                 | uu____1809 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1759 with
                                                | (b1,b2,body) ->
                                                    let env0 =
                                                      let uu____1831 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1831 [b1; b2] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1842 =
                                                          let uu____1843 =
                                                            let uu____1853 =
                                                              let uu____1857
                                                                =
                                                                let uu____1860
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b1) in
                                                                let uu____1861
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1860,
                                                                  uu____1861) in
                                                              [uu____1857] in
                                                            (wp_type,
                                                              uu____1853) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1843 in
                                                        mk uu____1842 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1869 =
                                                      let uu____1879 =
                                                        let uu____1880 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          body uu____1880 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1879 in
                                                    (match uu____1869 with
                                                     | (bs,body,what') ->
                                                         let fail uu____1908
                                                           =
                                                           let error_msg =
                                                             let uu____1910 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body in
                                                             let uu____1911 =
                                                               match what'
                                                               with
                                                               | None  ->
                                                                   "None"
                                                               | Some
                                                                   (FStar_Util.Inl
                                                                   lc) ->
                                                                   FStar_Syntax_Print.lcomp_to_string
                                                                    lc
                                                               | Some
                                                                   (FStar_Util.Inr
                                                                   (lid,uu____1927))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1910
                                                               uu____1911 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1953
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               (match uu____1953
                                                                with
                                                                | true  ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    env
                                                                    lc.FStar_Syntax_Syntax.res_typ
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    (match g_opt
                                                                    with
                                                                    | 
                                                                    Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env g'
                                                                    | 
                                                                    None  ->
                                                                    fail ())
                                                                | uu____1957
                                                                    ->
                                                                    fail ())
                                                           | Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____1959))
                                                               ->
                                                               (match 
                                                                  Prims.op_Negation
                                                                    (
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                                with
                                                                | true  ->
                                                                    fail ()
                                                                | uu____1970
                                                                    -> ()));
                                                          (let wp =
                                                             let t2 =
                                                               (Prims.fst b2).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type in
                                                           let body =
                                                             let uu____1979 =
                                                               let uu____1980
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1981
                                                                 =
                                                                 let uu____1982
                                                                   =
                                                                   let uu____1986
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b2] body
                                                                    what' in
                                                                   (uu____1986,
                                                                    None) in
                                                                 [uu____1982] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1980
                                                                 uu____1981 in
                                                             uu____1979 None
                                                               FStar_Range.dummyRange in
                                                           let uu____2002 =
                                                             let uu____2006 =
                                                               let uu____2010
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____2010] in
                                                             b1 :: uu____2006 in
                                                           let uu____2013 =
                                                             FStar_Syntax_Util.abs
                                                               bs body what in
                                                           FStar_Syntax_Util.abs
                                                             uu____2002
                                                             uu____2013
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____2023 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp =
                                           let uu____2025 =
                                             let uu____2026 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2026.FStar_Syntax_Syntax.n in
                                           match uu____2025 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2064 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2064
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2080 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp =
                                           let uu____2082 =
                                             let uu____2083 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2083.FStar_Syntax_Syntax.n in
                                           match uu____2082 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let uu____2112 =
                                                 let uu____2116 =
                                                   let uu____2118 =
                                                     let uu____2119 =
                                                       mk
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2119 in
                                                   [uu____2118] in
                                                 FStar_List.append uu____2116
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2112 body what
                                           | uu____2120 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           match (FStar_List.length
                                                    effect_binders)
                                                   = (Prims.parse_int "0")
                                           with
                                           | true  -> t
                                           | uu____2137 ->
                                               let uu____2138 =
                                                 let uu____2139 =
                                                   let uu____2140 =
                                                     let uu____2150 =
                                                       let uu____2151 =
                                                         FStar_Syntax_Util.args_of_binders
                                                           effect_binders in
                                                       Prims.snd uu____2151 in
                                                     (t, uu____2150) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____2140 in
                                                 mk uu____2139 in
                                               FStar_Syntax_Subst.close
                                                 effect_binders uu____2138 in
                                         let register name item =
                                           let uu____2163 =
                                             let uu____2166 = mk_lid name in
                                             let uu____2167 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders item None in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env uu____2166 uu____2167 in
                                           match uu____2163 with
                                           | (sigelt,fv) ->
                                               ((let uu____2176 =
                                                   let uu____2178 =
                                                     FStar_ST.read sigelts in
                                                   sigelt :: uu____2178 in
                                                 FStar_ST.write sigelts
                                                   uu____2176);
                                                fv) in
                                         let lift_from_pure_wp =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp =
                                           register "return_wp" return_wp in
                                         ((let uu____2189 =
                                             let uu____2191 =
                                               FStar_ST.read sigelts in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____2191 in
                                           FStar_ST.write sigelts uu____2189);
                                          (let return_elab =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2201 =
                                              let uu____2203 =
                                                FStar_ST.read sigelts in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: uu____2203 in
                                            FStar_ST.write sigelts uu____2201);
                                           (let bind_wp =
                                              register "bind_wp" bind_wp in
                                            (let uu____2213 =
                                               let uu____2215 =
                                                 FStar_ST.read sigelts in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: uu____2215 in
                                             FStar_ST.write sigelts
                                               uu____2213);
                                            (let bind_elab =
                                               register "bind_elab" bind_elab in
                                             (let uu____2225 =
                                                let uu____2227 =
                                                  FStar_ST.read sigelts in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: uu____2227 in
                                              FStar_ST.write sigelts
                                                uu____2225);
                                             (let uu____2235 =
                                                FStar_List.fold_left
                                                  (fun uu____2242  ->
                                                     fun action  ->
                                                       match uu____2242 with
                                                       | (dmff_env,actions)
                                                           ->
                                                           let uu____2254 =
                                                             elaborate_and_star
                                                               dmff_env
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu____2254
                                                            with
                                                            | (dmff_env,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env
                                                                    action_t
                                                                    action_wp in
                                                                let action_elab
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab in
                                                                let action_typ_with_wp
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp in
                                                                let uu____2270
                                                                  =
                                                                  let uu____2272
                                                                    =
                                                                    let uu___93_2273
                                                                    = action in
                                                                    let uu____2274
                                                                    =
                                                                    apply_close
                                                                    action_elab in
                                                                    let uu____2275
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___93_2273.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___93_2273.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___93_2273.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2274;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2275
                                                                    } in
                                                                  uu____2272
                                                                    ::
                                                                    actions in
                                                                (dmff_env,
                                                                  uu____2270)))
                                                  (dmff_env, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2235 with
                                              | (dmff_env,actions) ->
                                                  let actions =
                                                    FStar_List.rev actions in
                                                  let repr =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let uu____2293 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
                                                      let uu____2294 =
                                                        let uu____2296 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2296] in
                                                      uu____2293 ::
                                                        uu____2294 in
                                                    let uu____2297 =
                                                      let uu____2298 =
                                                        let uu____2299 =
                                                          let uu____2300 =
                                                            let uu____2310 =
                                                              let uu____2314
                                                                =
                                                                let uu____2317
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                let uu____2318
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2317,
                                                                  uu____2318) in
                                                              [uu____2314] in
                                                            (repr,
                                                              uu____2310) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2300 in
                                                        mk uu____2299 in
                                                      let uu____2326 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env uu____2298
                                                        uu____2326 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2297 None in
                                                  let repr =
                                                    recheck_debug "FC" env
                                                      repr in
                                                  let repr =
                                                    register "repr" repr in
                                                  let uu____2334 =
                                                    let uu____2339 =
                                                      let uu____2340 =
                                                        let uu____2343 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2343 in
                                                      uu____2340.FStar_Syntax_Syntax.n in
                                                    match uu____2339 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow,uu____2351)
                                                        ->
                                                        let uu____2378 =
                                                          let uu____2387 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow in
                                                          match uu____2387
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2418 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2378
                                                         with
                                                         | (type_param,effect_param,arrow)
                                                             ->
                                                             let uu____2446 =
                                                               let uu____2447
                                                                 =
                                                                 let uu____2450
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2450 in
                                                               uu____2447.FStar_Syntax_Syntax.n in
                                                             (match uu____2446
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2467
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____2467
                                                                   with
                                                                   | 
                                                                   (wp_binders,c)
                                                                    ->
                                                                    let uu____2476
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2487
                                                                     ->
                                                                    match uu____2487
                                                                    with
                                                                    | 
                                                                    (bv,uu____2491)
                                                                    ->
                                                                    let uu____2492
                                                                    =
                                                                    let uu____2493
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____2493
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param)) in
                                                                    FStar_All.pipe_right
                                                                    uu____2492
                                                                    Prims.op_Negation)
                                                                    wp_binders in
                                                                    (match uu____2476
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
                                                                    uu____2526
                                                                    ->
                                                                    let uu____2530
                                                                    =
                                                                    let uu____2531
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2531 in
                                                                    failwith
                                                                    uu____2530 in
                                                                    let uu____2534
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c in
                                                                    let uu____2537
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (uu____2534,
                                                                    uu____2537)))
                                                              | uu____2547 ->
                                                                  let uu____2548
                                                                    =
                                                                    let uu____2549
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2549 in
                                                                  failwith
                                                                    uu____2548))
                                                    | uu____2554 ->
                                                        let uu____2555 =
                                                          let uu____2556 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2556 in
                                                        failwith uu____2555 in
                                                  (match uu____2334 with
                                                   | (pre,post) ->
                                                       ((let uu____2573 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2575 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2577 =
                                                           register "wp"
                                                             wp_type in
                                                         ());
                                                        (let ed =
                                                           let uu___94_2579 =
                                                             ed in
                                                           let uu____2580 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders in
                                                           let uu____2581 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders
                                                               effect_signature in
                                                           let uu____2582 =
                                                             let uu____2583 =
                                                               apply_close
                                                                 return_wp in
                                                             ([], uu____2583) in
                                                           let uu____2589 =
                                                             let uu____2590 =
                                                               apply_close
                                                                 bind_wp in
                                                             ([], uu____2590) in
                                                           let uu____2596 =
                                                             apply_close repr in
                                                           let uu____2597 =
                                                             let uu____2598 =
                                                               apply_close
                                                                 return_elab in
                                                             ([], uu____2598) in
                                                           let uu____2604 =
                                                             let uu____2605 =
                                                               apply_close
                                                                 bind_elab in
                                                             ([], uu____2605) in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2580;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2581;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2582;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2589;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___94_2579.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2596;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2597;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2604;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions
                                                           } in
                                                         let uu____2611 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env
                                                             effect_binders a
                                                             wp_a ed in
                                                         match uu____2611
                                                         with
                                                         | (sigelts',ed) ->
                                                             ((let uu____2622
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               match uu____2622
                                                               with
                                                               | true  ->
                                                                   let uu____2623
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed in
                                                                   FStar_Util.print_string
                                                                    uu____2623
                                                               | uu____2624
                                                                   -> ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 match 
                                                                   (FStar_List.length
                                                                    effect_binders)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 with
                                                                 | true  ->
                                                                    let lift_from_pure
                                                                    =
                                                                    let uu____2633
                                                                    =
                                                                    let uu____2635
                                                                    =
                                                                    let uu____2641
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp in
                                                                    ([],
                                                                    uu____2641) in
                                                                    Some
                                                                    uu____2635 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____2633;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                    Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 | uu____2652
                                                                    -> None in
                                                               let uu____2653
                                                                 =
                                                                 let uu____2655
                                                                   =
                                                                   let uu____2657
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____2657 in
                                                                 FStar_List.append
                                                                   uu____2655
                                                                   sigelts' in
                                                               (uu____2653,
                                                                 ed,
                                                                 lift_from_pure_opt))))))))))))))))))
and tc_lex_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          match ses with
          | (FStar_Syntax_Syntax.Sig_inductive_typ
              (lex_t,[],[],t,uu____2680,uu____2681,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top,[],_t_top,_lex_t_top,_0_28,[],uu____2686,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2691,r2))::[]
              when
              ((_0_28 = (Prims.parse_int "0")) &&
                 (_0_29 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r in
              let t = FStar_Syntax_Subst.close_univ_vars [u] t in
              let tc =
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t, [u], [], t, [],
                    [FStar_Syntax_Const.lextop_lid;
                    FStar_Syntax_Const.lexcons_lid], [], r) in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                let uu____2735 =
                  let uu____2738 =
                    let uu____2739 =
                      let uu____2744 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2744, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2739 in
                  FStar_Syntax_Syntax.mk uu____2738 in
                uu____2735 None r1 in
              let lex_top_t =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top, [utop], lex_top_t, FStar_Syntax_Const.lex_t_lid,
                    (Prims.parse_int "0"), [], [], r1) in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2765 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2765 in
                let hd =
                  let uu____2771 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2771 in
                let tl =
                  let uu____2773 =
                    let uu____2774 =
                      let uu____2777 =
                        let uu____2778 =
                          let uu____2783 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2783, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2778 in
                      FStar_Syntax_Syntax.mk uu____2777 in
                    uu____2774 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2773 in
                let res =
                  let uu____2796 =
                    let uu____2799 =
                      let uu____2800 =
                        let uu____2805 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2805,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2800 in
                    FStar_Syntax_Syntax.mk uu____2799 in
                  uu____2796 None r2 in
                let uu____2815 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd, None);
                  (tl, None)] uu____2815 in
              let lex_cons_t =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r2) in
              let uu____2838 =
                let uu____2846 = FStar_TypeChecker_Env.get_range env in
                ([tc; dc_lextop; dc_lexcons], [], lids, uu____2846) in
              FStar_Syntax_Syntax.Sig_bundle uu____2838
          | uu____2850 ->
              let uu____2852 =
                let uu____2853 =
                  FStar_Syntax_Print.sigelt_to_string
                    (FStar_Syntax_Syntax.Sig_bundle
                       (ses, [], lids, FStar_Range.dummyRange)) in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2853 in
              failwith uu____2852
and tc_assume:
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
            let env = FStar_TypeChecker_Env.set_range env r in
            let uu____2864 = FStar_Syntax_Util.type_u () in
            match uu____2864 with
            | (k,uu____2868) ->
                let phi =
                  let uu____2870 = tc_check_trivial_guard env phi k in
                  FStar_All.pipe_right uu____2870
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env) in
                (FStar_TypeChecker_Util.check_uvars r phi;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r))
and tc_inductive:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env in
          let uu____2881 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2881 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2900 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right uu____2900 FStar_List.flatten in
              ((let uu____2908 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                match uu____2908 with
                | true  -> ()
                | uu____2909 ->
                    let env =
                      FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                    FStar_List.iter
                      (fun ty  ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env in
                         match Prims.op_Negation b with
                         | true  ->
                             let uu____2914 =
                               match ty with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   (lid,uu____2920,uu____2921,uu____2922,uu____2923,uu____2924,uu____2925,r)
                                   -> (lid, r)
                               | uu____2933 -> failwith "Impossible!" in
                             (match uu____2914 with
                              | (lid,r) ->
                                  FStar_Errors.report r
                                    (Prims.strcat "Inductive type "
                                       (Prims.strcat lid.FStar_Ident.str
                                          " does not satisfy the positivity condition")))
                         | uu____2938 -> ()) tcs);
               (let skip_prims_type uu____2942 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2946,uu____2947,uu____2948,uu____2949,uu____2950,uu____2951,uu____2952)
                        -> lid
                    | uu____2959 -> failwith "Impossible" in
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
                let uu____2965 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                match uu____2965 with
                | true  -> ([sig_bndle], data_ops_ses)
                | uu____2974 ->
                    let is_unopteq =
                      FStar_List.existsb
                        (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                    let ses =
                      match is_unopteq with
                      | true  ->
                          FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                            sig_bndle tcs datas env0 tc_assume
                      | uu____2980 ->
                          FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                            sig_bndle tcs datas env0 tc_assume in
                    let uu____2981 =
                      let uu____2983 =
                        let uu____2984 =
                          let uu____2992 =
                            FStar_TypeChecker_Env.get_range env0 in
                          ((FStar_List.append tcs datas), quals, lids,
                            uu____2992) in
                        FStar_Syntax_Syntax.Sig_bundle uu____2984 in
                      uu____2983 :: ses in
                    (uu____2981, data_ops_ses)))
and tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (match se with
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let se = tc_lex_t env ses quals lids in
           let uu____3032 = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], uu____3032, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____3046 = tc_inductive env ses quals lids in
           (match uu____3046 with
            | (ses,projectors_ses) ->
                let env =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se  -> FStar_TypeChecker_Env.push_sigelt env' se)
                    env ses in
                (ses, env, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options t s =
             let uu____3076 = FStar_Options.set_options t s in
             match uu____3076 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                ((match p = FStar_Syntax_Syntax.LightOff with
                  | true  -> FStar_Options.set_ml_ish ()
                  | uu____3084 -> ());
                 ([se], env, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options FStar_Options.Set o; ([se], env, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____3094 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3094 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options FStar_Options.Reset s);
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3100 ->
           failwith "impossible"
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne = tc_eff_decl env ne in
           let se = FStar_Syntax_Syntax.Sig_new_effect (ne, r) in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           let uu____3113 =
             FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____3124  ->
                     fun a  ->
                       match uu____3124 with
                       | (env,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne.FStar_Syntax_Syntax.mname a in
                           let uu____3137 =
                             FStar_TypeChecker_Env.push_sigelt env se_let in
                           (uu____3137, (se_let :: ses))) (env, [se])) in
           (match uu____3113 with | (env,ses) -> ([se], env, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub,r) ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.target in
           let uu____3155 =
             let uu____3160 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____3160 in
           (match uu____3155 with
            | (a,wp_a_src) ->
                let uu____3172 =
                  let uu____3177 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub.FStar_Syntax_Syntax.target in
                  monad_signature env sub.FStar_Syntax_Syntax.target
                    uu____3177 in
                (match uu____3172 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3190 =
                         let uu____3192 =
                           let uu____3193 =
                             let uu____3198 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3198) in
                           FStar_Syntax_Syntax.NT uu____3193 in
                         [uu____3192] in
                       FStar_Syntax_Subst.subst uu____3190 wp_b_tgt in
                     let expected_k =
                       let uu____3202 =
                         let uu____3206 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3207 =
                           let uu____3209 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3209] in
                         uu____3206 :: uu____3207 in
                       let uu____3210 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3202 uu____3210 in
                     let repr_type eff_name a wp =
                       let no_reify l =
                         let uu____3231 =
                           let uu____3232 =
                             let uu____3235 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3236 =
                               FStar_TypeChecker_Env.get_range env in
                             (uu____3235, uu____3236) in
                           FStar_Errors.Error uu____3232 in
                         Prims.raise uu____3231 in
                       let uu____3239 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____3239 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____3246 =
                             let uu____3247 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3247 in
                           (match uu____3246 with
                            | true  -> no_reify eff_name
                            | uu____3251 ->
                                let uu____3252 =
                                  FStar_TypeChecker_Env.get_range env in
                                let uu____3253 =
                                  let uu____3256 =
                                    let uu____3257 =
                                      let uu____3267 =
                                        let uu____3269 =
                                          FStar_Syntax_Syntax.as_arg a in
                                        let uu____3270 =
                                          let uu____3272 =
                                            FStar_Syntax_Syntax.as_arg wp in
                                          [uu____3272] in
                                        uu____3269 :: uu____3270 in
                                      (repr, uu____3267) in
                                    FStar_Syntax_Syntax.Tm_app uu____3257 in
                                  FStar_Syntax_Syntax.mk uu____3256 in
                                uu____3253 None uu____3252) in
                     let uu____3282 =
                       match ((sub.FStar_Syntax_Syntax.lift),
                               (sub.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____3297,lift_wp)) ->
                           let uu____3310 =
                             check_and_gen env lift_wp expected_k in
                           (lift, uu____3310)
                       | (Some (what,lift),None ) ->
                           let dmff_env =
                             FStar_TypeChecker_DMFF.empty env
                               (FStar_TypeChecker_TcTerm.tc_constant
                                  FStar_Range.dummyRange) in
                           let uu____3325 =
                             FStar_TypeChecker_DMFF.star_expr dmff_env lift in
                           (match uu____3325 with
                            | (uu____3332,lift_wp,lift_elab) ->
                                let uu____3335 =
                                  recheck_debug "lift-wp" env lift_wp in
                                let uu____3336 =
                                  recheck_debug "lift-elab" env lift_elab in
                                ((Some ([], lift_elab)), ([], lift_wp))) in
                     (match uu____3282 with
                      | (lift,lift_wp) ->
                          let lax = env.FStar_TypeChecker_Env.lax in
                          let env =
                            let uu___95_3360 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___95_3360.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___95_3360.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___95_3360.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___95_3360.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___95_3360.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___95_3360.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___95_3360.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___95_3360.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___95_3360.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___95_3360.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___95_3360.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___95_3360.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___95_3360.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___95_3360.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___95_3360.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___95_3360.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___95_3360.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___95_3360.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___95_3360.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___95_3360.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___95_3360.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___95_3360.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___95_3360.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift =
                            match lift with
                            | None  -> None
                            | Some (uu____3364,lift) ->
                                let uu____3371 =
                                  let uu____3376 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env sub.FStar_Syntax_Syntax.source in
                                  monad_signature env
                                    sub.FStar_Syntax_Syntax.source uu____3376 in
                                (match uu____3371 with
                                 | (a,wp_a_src) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub.FStar_Syntax_Syntax.source a_typ
                                         wp_a_typ in
                                     let repr_result =
                                       let lift_wp =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env (Prims.snd lift_wp) in
                                       let lift_wp_a =
                                         let uu____3398 =
                                           FStar_TypeChecker_Env.get_range
                                             env in
                                         let uu____3399 =
                                           let uu____3402 =
                                             let uu____3403 =
                                               let uu____3413 =
                                                 let uu____3415 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3416 =
                                                   let uu____3418 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3418] in
                                                 uu____3415 :: uu____3416 in
                                               (lift_wp, uu____3413) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3403 in
                                           FStar_Syntax_Syntax.mk uu____3402 in
                                         uu____3399 None uu____3398 in
                                       repr_type
                                         sub.FStar_Syntax_Syntax.target a_typ
                                         lift_wp_a in
                                     let expected_k =
                                       let uu____3431 =
                                         let uu____3435 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____3436 =
                                           let uu____3438 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3439 =
                                             let uu____3441 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3441] in
                                           uu____3438 :: uu____3439 in
                                         uu____3435 :: uu____3436 in
                                       let uu____3442 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3431
                                         uu____3442 in
                                     let uu____3445 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env expected_k in
                                     (match uu____3445 with
                                      | (expected_k,uu____3451,uu____3452) ->
                                          let lift =
                                            check_and_gen env lift expected_k in
                                          Some lift)) in
                          let env =
                            let uu___96_3455 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___96_3455.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___96_3455.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___96_3455.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___96_3455.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___96_3455.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___96_3455.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___96_3455.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___96_3455.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___96_3455.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___96_3455.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___96_3455.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___96_3455.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___96_3455.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___96_3455.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___96_3455.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___96_3455.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___96_3455.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___96_3455.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___96_3455.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___96_3455.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___96_3455.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___96_3455.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___96_3455.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let sub =
                            let uu___97_3457 = sub in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___97_3457.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___97_3457.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift
                            } in
                          let se =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub, r) in
                          let env = FStar_TypeChecker_Env.push_sigelt env se in
                          ([se], env, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env in
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____3476 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3476 with
            | (tps,c) ->
                let uu____3486 = FStar_TypeChecker_TcTerm.tc_tparams env tps in
                (match uu____3486 with
                 | (tps,env,us) ->
                     let uu____3498 = FStar_TypeChecker_TcTerm.tc_comp env c in
                     (match uu____3498 with
                      | (c,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let tps = FStar_Syntax_Subst.close_binders tps in
                            let c = FStar_Syntax_Subst.close_comp tps c in
                            let uu____3513 =
                              let uu____3514 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3514 in
                            match uu____3513 with
                            | (uvs,t) ->
                                let uu____3528 =
                                  let uu____3536 =
                                    let uu____3539 =
                                      let uu____3540 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3540.FStar_Syntax_Syntax.n in
                                    (tps, uu____3539) in
                                  match uu____3536 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3550,c)) -> ([], c)
                                  | (uu____3574,FStar_Syntax_Syntax.Tm_arrow
                                     (tps,c)) -> (tps, c)
                                  | uu____3592 -> failwith "Impossible" in
                                (match uu____3528 with
                                 | (tps,c) ->
                                     ((match ((FStar_List.length uvs) <>
                                                (Prims.parse_int "1"))
                                               &&
                                               (Prims.op_Negation
                                                  (FStar_Ident.lid_equals lid
                                                     FStar_Syntax_Const.effect_Lemma_lid))
                                       with
                                       | true  ->
                                           let uu____3622 =
                                             FStar_Syntax_Subst.open_univ_vars
                                               uvs t in
                                           (match uu____3622 with
                                            | (uu____3625,t) ->
                                                let uu____3627 =
                                                  let uu____3628 =
                                                    let uu____3631 =
                                                      let uu____3632 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid in
                                                      let uu____3633 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs)
                                                          FStar_Util.string_of_int in
                                                      let uu____3636 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____3632 uu____3633
                                                        uu____3636 in
                                                    (uu____3631, r) in
                                                  FStar_Errors.Error
                                                    uu____3628 in
                                                Prims.raise uu____3627)
                                       | uu____3637 -> ());
                                      (let se =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs, tps, c, tags, flags, r) in
                                       let env =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se in
                                       ([se], env, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___77_3666  ->
                   match uu___77_3666 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3667 -> false))
           -> ([], env, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____3678 =
             match uvs = [] with
             | true  ->
                 let uu____3679 =
                   let uu____3680 = FStar_Syntax_Util.type_u () in
                   Prims.fst uu____3680 in
                 check_and_gen env t uu____3679
             | uu____3683 ->
                 let uu____3684 = FStar_Syntax_Subst.open_univ_vars uvs t in
                 (match uu____3684 with
                  | (uvs,t) ->
                      let uu____3689 =
                        let uu____3690 =
                          let uu____3691 =
                            let uu____3692 = FStar_Syntax_Util.type_u () in
                            Prims.fst uu____3692 in
                          tc_check_trivial_guard env t uu____3691 in
                        FStar_All.pipe_left
                          (FStar_Syntax_Subst.close_univ_vars uvs) uu____3690 in
                      (uvs, uu____3689)) in
           (match uu____3678 with
            | (uvs,t) ->
                let se =
                  FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) in
                let env = FStar_TypeChecker_Env.push_sigelt env se in
                ([se], env, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se = tc_assume env lid phi quals r in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], env, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let env =
             FStar_TypeChecker_Env.set_expected_typ env
               FStar_TypeChecker_Common.t_unit in
           let uu____3724 = FStar_TypeChecker_TcTerm.tc_term env e in
           (match uu____3724 with
            | (e,c,g1) ->
                let uu____3736 =
                  let uu____3740 =
                    let uu____3742 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3742 in
                  let uu____3743 =
                    let uu____3746 = c.FStar_Syntax_Syntax.comp () in
                    (e, uu____3746) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env
                    uu____3740 uu____3743 in
                (match uu____3736 with
                 | (e,uu____3757,g) ->
                     ((let uu____3760 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env
                         uu____3760);
                      (let se = FStar_Syntax_Syntax.Sig_main (e, r) in
                       let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3802 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 (match uu____3802 with
                  | true  -> Some q
                  | uu____3810 ->
                      let uu____3811 =
                        let uu____3812 =
                          let uu____3815 =
                            let uu____3816 =
                              FStar_Syntax_Print.lid_to_string l in
                            let uu____3817 =
                              FStar_Syntax_Print.quals_to_string q in
                            let uu____3818 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____3816 uu____3817 uu____3818 in
                          (uu____3815, r) in
                        FStar_Errors.Error uu____3812 in
                      Prims.raise uu____3811) in
           let uu____3821 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3842  ->
                     fun lb  ->
                       match uu____3842 with
                       | (gen,lbs,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3866 =
                             let uu____3872 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3872 with
                             | None  ->
                                 (match lb.FStar_Syntax_Syntax.lbunivs <> []
                                  with
                                  | true  -> (false, lb, quals_opt)
                                  | uu____3897 -> (gen, lb, quals_opt))
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3924 ->
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  (match (lb.FStar_Syntax_Syntax.lbunivs <>
                                            [])
                                           &&
                                           ((FStar_List.length
                                               lb.FStar_Syntax_Syntax.lbunivs)
                                              <> (FStar_List.length uvs))
                                   with
                                   | true  ->
                                       Prims.raise
                                         (FStar_Errors.Error
                                            ("Inline universes are incoherent with annotation from val declaration",
                                              r))
                                   | uu____3931 -> ());
                                  (let uu____3932 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, uu____3932, quals_opt))) in
                           (match uu____3866 with
                            | (gen,lb,quals_opt) ->
                                (gen, (lb :: lbs), quals_opt)))
                  (true, [],
                    (match quals = [] with
                     | true  -> None
                     | uu____3963 -> Some quals))) in
           (match uu____3821 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3986 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___78_3988  ->
                                match uu___78_3988 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3989 -> false)) in
                      (match uu____3986 with
                       | true  -> q
                       | uu____3991 -> FStar_Syntax_Syntax.Visible_default ::
                           q) in
                let lbs' = FStar_List.rev lbs' in
                let e =
                  let uu____3997 =
                    let uu____4000 =
                      let uu____4001 =
                        let uu____4009 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((Prims.fst lbs), lbs'), uu____4009) in
                      FStar_Syntax_Syntax.Tm_let uu____4001 in
                    FStar_Syntax_Syntax.mk uu____4000 in
                  uu____3997 None r in
                let uu____4031 =
                  let uu____4037 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___98_4041 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___98_4041.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___98_4041.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___98_4041.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___98_4041.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___98_4041.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___98_4041.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___98_4041.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___98_4041.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___98_4041.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___98_4041.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___98_4041.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___98_4041.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___98_4041.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___98_4041.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___98_4041.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___98_4041.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___98_4041.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___98_4041.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___98_4041.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___98_4041.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___98_4041.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___98_4041.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____4037 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs,e);
                       FStar_Syntax_Syntax.tk = uu____4049;
                       FStar_Syntax_Syntax.pos = uu____4050;
                       FStar_Syntax_Syntax.vars = uu____4051;_},uu____4052,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals =
                        match e.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____4071,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4076 -> quals in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs, r, lids, quals, attrs)), lbs)
                  | uu____4086 -> failwith "impossible" in
                (match uu____4031 with
                 | (se,lbs) ->
                     ((let uu____4109 = log env in
                       match uu____4109 with
                       | true  ->
                           let uu____4110 =
                             let uu____4111 =
                               FStar_All.pipe_right (Prims.snd lbs)
                                 (FStar_List.map
                                    (fun lb  ->
                                       let should_log =
                                         let uu____4118 =
                                           let uu____4123 =
                                             let uu____4124 =
                                               let uu____4129 =
                                                 FStar_Util.right
                                                   lb.FStar_Syntax_Syntax.lbname in
                                               uu____4129.FStar_Syntax_Syntax.fv_name in
                                             uu____4124.FStar_Syntax_Syntax.v in
                                           FStar_TypeChecker_Env.try_lookup_val_decl
                                             env uu____4123 in
                                         match uu____4118 with
                                         | None  -> true
                                         | uu____4136 -> false in
                                       match should_log with
                                       | true  ->
                                           let uu____4141 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lb.FStar_Syntax_Syntax.lbname in
                                           let uu____4142 =
                                             FStar_Syntax_Print.term_to_string
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           FStar_Util.format2 "let %s : %s"
                                             uu____4141 uu____4142
                                       | uu____4143 -> "")) in
                             FStar_All.pipe_right uu____4111
                               (FStar_String.concat "\n") in
                           FStar_Util.print1 "%s\n" uu____4110
                       | uu____4145 -> ());
                      (let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___79_4172  ->
                match uu___79_4172 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4173 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4181 -> false in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____4186 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4199,r) ->
          let uu____4207 = is_abstract quals in
          (match uu____4207 with
           | true  ->
               FStar_List.fold_right
                 (fun se  ->
                    fun uu____4217  ->
                      match uu____4217 with
                      | (out,hidden) ->
                          (match se with
                           | FStar_Syntax_Syntax.Sig_inductive_typ
                               (l,us,bs,t,uu____4240,uu____4241,quals,r) ->
                               let dec =
                                 let uu____4251 =
                                   let uu____4258 =
                                     let uu____4261 =
                                       FStar_Syntax_Syntax.mk_Total t in
                                     FStar_Syntax_Util.arrow bs uu____4261 in
                                   (l, us, uu____4258,
                                     (FStar_Syntax_Syntax.Assumption ::
                                     FStar_Syntax_Syntax.New :: quals), r) in
                                 FStar_Syntax_Syntax.Sig_declare_typ
                                   uu____4251 in
                               ((dec :: out), hidden)
                           | FStar_Syntax_Syntax.Sig_datacon
                               (l,us,t,uu____4272,uu____4273,uu____4274,uu____4275,r)
                               ->
                               let dec =
                                 FStar_Syntax_Syntax.Sig_declare_typ
                                   (l, us, t,
                                     [FStar_Syntax_Syntax.Assumption], r) in
                               ((dec :: out), (l :: hidden))
                           | uu____4285 -> (out, hidden))) ses ([], hidden)
           | uu____4290 -> ([se], hidden))
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4293,uu____4294,quals,uu____4296) ->
          let uu____4299 = is_abstract quals in
          (match uu____4299 with
           | true  -> ([], hidden)
           | uu____4306 -> ([se], hidden))
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4316 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          (match uu____4316 with
           | true  ->
               ([FStar_Syntax_Syntax.Sig_declare_typ
                   (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
                 hidden))
           | uu____4325 ->
               let uu____4326 =
                 FStar_All.pipe_right quals
                   (FStar_Util.for_some
                      (fun uu___80_4328  ->
                         match uu___80_4328 with
                         | FStar_Syntax_Syntax.Assumption 
                           |FStar_Syntax_Syntax.Projector _
                            |FStar_Syntax_Syntax.Discriminator _ -> true
                         | uu____4331 -> false)) in
               (match uu____4326 with
                | true  -> ([se], hidden)
                | uu____4338 -> ([], hidden)))
      | FStar_Syntax_Syntax.Sig_main uu____4341 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4353,uu____4354,quals,uu____4356) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____4374 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          (match uu____4374 with
           | true  -> ([], hidden)
           | uu____4382 ->
               let dec =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                     (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp),
                     [FStar_Syntax_Syntax.Assumption],
                     (FStar_Ident.range_of_lid lid)) in
               ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4398) ->
          let uu____4405 = is_abstract quals in
          (match uu____4405 with
           | true  ->
               let uu____4410 =
                 FStar_All.pipe_right (Prims.snd lbs)
                   (FStar_List.map
                      (fun lb  ->
                         let uu____4416 =
                           let uu____4423 =
                             let uu____4424 =
                               let uu____4429 =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               uu____4429.FStar_Syntax_Syntax.fv_name in
                             uu____4424.FStar_Syntax_Syntax.v in
                           (uu____4423, (lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp),
                             (FStar_Syntax_Syntax.Assumption :: quals), r) in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4416)) in
               (uu____4410, hidden)
           | uu____4439 -> ([se], hidden))
let tc_decls:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env_t)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4476 se =
        match uu____4476 with
        | (ses,exports,env,hidden) ->
            ((let uu____4507 =
                FStar_TypeChecker_Env.debug env FStar_Options.Low in
              match uu____4507 with
              | true  ->
                  let uu____4508 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Util.print1
                    ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4508
              | uu____4509 -> ());
             (let uu____4510 = tc_decl env se in
              match uu____4510 with
              | (ses',env,ses_elaborated) ->
                  ((let uu____4532 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LogTypes")) in
                    match uu____4532 with
                    | true  ->
                        let uu____4533 =
                          FStar_List.fold_left
                            (fun s  ->
                               fun se  ->
                                 let uu____4536 =
                                   let uu____4537 =
                                     FStar_Syntax_Print.sigelt_to_string se in
                                   Prims.strcat uu____4537 "\n" in
                                 Prims.strcat s uu____4536) "" ses' in
                        FStar_Util.print1 "Checked: %s\n" uu____4533
                    | uu____4538 -> ());
                   FStar_List.iter
                     (fun se  ->
                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env se) ses';
                   (let uu____4541 =
                      FStar_List.fold_left
                        (fun uu____4550  ->
                           fun se  ->
                             match uu____4550 with
                             | (le,lh) ->
                                 let tup = for_export hidden se in
                                 ((FStar_List.rev_append (Prims.fst tup) le),
                                   (FStar_List.rev_append (Prims.snd tup) lh)))
                        ([], []) ses' in
                    match uu____4541 with
                    | (exported,hidden) ->
                        FStar_List.fold_left process_one_decl
                          ((FStar_List.rev_append ses' ses),
                            ((FStar_List.rev_append exported []) :: exports),
                            env, hidden) ses_elaborated)))) in
      let uu____4606 =
        FStar_List.fold_left
          (fun acc  ->
             fun se  ->
               match se with
               | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
                   let uu____4643 = acc in
                   (match uu____4643 with
                    | (uu____4660,uu____4661,env,uu____4663) ->
                        let uu____4672 = cps_and_elaborate env ne in
                        (match uu____4672 with
                         | (ses,ne,lift_from_pure_opt) ->
                             let ses =
                               match lift_from_pure_opt with
                               | Some lift ->
                                   FStar_List.append ses
                                     [FStar_Syntax_Syntax.Sig_new_effect
                                        (ne, r);
                                     lift]
                               | None  ->
                                   FStar_List.append ses
                                     [FStar_Syntax_Syntax.Sig_new_effect
                                        (ne, r)] in
                             FStar_List.fold_left process_one_decl acc ses))
               | uu____4705 -> process_one_decl acc se) ([], [], env, []) ses in
      match uu____4606 with
      | (ses,exports,env,uu____4719) ->
          let uu____4728 =
            FStar_All.pipe_right (FStar_List.rev_append exports [])
              FStar_List.flatten in
          ((FStar_List.rev_append ses []), uu____4728, env)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action =
        match verify with
        | true  -> "Verifying"
        | uu____4749 -> "Lax-checking" in
      let label =
        match modul.FStar_Syntax_Syntax.is_interface with
        | true  -> "interface"
        | uu____4751 -> "implementation" in
      (let uu____4753 = FStar_Options.debug_any () in
       match uu____4753 with
       | true  ->
           FStar_Util.print3 "%s %s of %s\n" action label
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       | uu____4754 -> ());
      (let name =
         FStar_Util.format2 "%s %s"
           (match modul.FStar_Syntax_Syntax.is_interface with
            | true  -> "interface"
            | uu____4756 -> "module")
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let msg = Prims.strcat "Internals for " name in
       let env =
         let uu___99_4759 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___99_4759.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___99_4759.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___99_4759.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___99_4759.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___99_4759.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___99_4759.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___99_4759.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___99_4759.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___99_4759.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___99_4759.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___99_4759.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___99_4759.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___99_4759.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___99_4759.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___99_4759.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___99_4759.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___99_4759.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___99_4759.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___99_4759.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___99_4759.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___99_4759.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___99_4759.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env =
          FStar_TypeChecker_Env.set_current_module env
            modul.FStar_Syntax_Syntax.name in
        let uu____4762 = tc_decls env modul.FStar_Syntax_Syntax.declarations in
        match uu____4762 with
        | (ses,exports,env) ->
            ((let uu___100_4780 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___100_4780.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___100_4780.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___100_4780.FStar_Syntax_Syntax.is_interface)
              }), exports, env)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____4796 = tc_decls env decls in
        match uu____4796 with
        | (ses,exports,env) ->
            let modul =
              let uu___101_4814 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_4814.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___101_4814.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_4814.FStar_Syntax_Syntax.is_interface)
              } in
            (modul, exports, env)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env =
          let uu___102_4828 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___102_4828.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___102_4828.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___102_4828.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___102_4828.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___102_4828.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___102_4828.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___102_4828.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___102_4828.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___102_4828.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___102_4828.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___102_4828.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___102_4828.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___102_4828.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___102_4828.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___102_4828.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___102_4828.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___102_4828.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___102_4828.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___102_4828.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___102_4828.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___102_4828.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs t =
          let uu____4839 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____4839 with
          | (univs,t) ->
              ((let uu____4845 =
                  let uu____4846 =
                    let uu____4849 =
                      FStar_TypeChecker_Env.set_current_module env
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4849 in
                  FStar_All.pipe_left uu____4846
                    (FStar_Options.Other "Exports") in
                match uu____4845 with
                | true  ->
                    let uu____4850 = FStar_Syntax_Print.lid_to_string lid in
                    let uu____4851 =
                      let uu____4852 =
                        FStar_All.pipe_right univs
                          (FStar_List.map
                             (fun x  ->
                                FStar_Syntax_Print.univ_to_string
                                  (FStar_Syntax_Syntax.U_name x))) in
                      FStar_All.pipe_right uu____4852
                        (FStar_String.concat ", ") in
                    let uu____4857 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                      uu____4850 uu____4851 uu____4857
                | uu____4858 -> ());
               (let env = FStar_TypeChecker_Env.push_univ_vars env univs in
                let uu____4860 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env t in
                FStar_All.pipe_right uu____4860 Prims.ignore)) in
        let check_term lid univs t =
          (let uu____4878 =
             let uu____4879 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____4880 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4879 uu____4880 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4878);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt uu___81_4885 =
          match uu___81_4885 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4888,uu____4889)
              ->
              let uu____4896 =
                let uu____4897 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4897 in
              (match uu____4896 with
               | true  ->
                   FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
               | uu____4900 -> ())
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____4905,uu____4906,uu____4907,r) ->
              let t =
                let uu____4918 =
                  let uu____4921 =
                    let uu____4922 =
                      let uu____4930 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____4930) in
                    FStar_Syntax_Syntax.Tm_arrow uu____4922 in
                  FStar_Syntax_Syntax.mk uu____4921 in
                uu____4918 None r in
              check_term l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____4942,uu____4943,uu____4944,uu____4945,uu____4946)
              -> check_term l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t,quals,uu____4955)
              ->
              let uu____4958 =
                let uu____4959 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4959 in
              (match uu____4958 with
               | true  -> check_term l univs t
               | uu____4961 -> ())
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4962,lbs),uu____4964,uu____4965,quals,uu____4967) ->
              let uu____4979 =
                let uu____4980 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____4980 in
              (match uu____4979 with
               | true  ->
                   FStar_All.pipe_right lbs
                     (FStar_List.iter
                        (fun lb  ->
                           let fv =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           check_term
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbtyp))
               | uu____4989 -> ())
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs,binders,comp,quals,flags,r) ->
              let uu____5001 =
                let uu____5002 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5002 in
              (match uu____5001 with
               | true  ->
                   let arrow =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None
                       r in
                   check_term l univs arrow
               | uu____5015 -> ())
          | FStar_Syntax_Syntax.Sig_main _
            |FStar_Syntax_Syntax.Sig_assume _
             |FStar_Syntax_Syntax.Sig_new_effect _
              |FStar_Syntax_Syntax.Sig_new_effect_for_free _
               |FStar_Syntax_Syntax.Sig_sub_effect _
                |FStar_Syntax_Syntax.Sig_pragma _
              -> () in
        match FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
                FStar_Syntax_Const.prims_lid
        with
        | true  -> ()
        | uu____5022 -> FStar_List.iter check_sigelt exports
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul =
          let uu___103_5035 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___103_5035.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___103_5035.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env = FStar_TypeChecker_Env.finish_module env modul in
        (let uu____5038 =
           let uu____5039 = FStar_Options.lax () in
           Prims.op_Negation uu____5039 in
         match uu____5038 with
         | true  -> check_exports env modul exports
         | uu____5040 -> ());
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env modul;
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____5045 =
           let uu____5046 = FStar_Options.interactive () in
           Prims.op_Negation uu____5046 in
         match uu____5045 with
         | true  ->
             let uu____5047 = FStar_Options.restore_cmd_line_options true in
             FStar_All.pipe_right uu____5047 Prims.ignore
         | uu____5048 -> ());
        (modul, env)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____5057 = tc_partial_modul env modul in
      match uu____5057 with
      | (modul,non_private_decls,env) ->
          finish_partial_modul env modul non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____5078 = FStar_Options.debug_any () in
       match uu____5078 with
       | true  ->
           let uu____5079 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (match m.FStar_Syntax_Syntax.is_interface with
              | true  -> "i'face"
              | uu____5080 -> "module") uu____5079
       | uu____5081 -> ());
      (let env =
         let uu___104_5083 = env in
         let uu____5084 =
           let uu____5085 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5085 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___104_5083.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___104_5083.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___104_5083.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___104_5083.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___104_5083.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___104_5083.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___104_5083.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___104_5083.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___104_5083.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___104_5083.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___104_5083.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___104_5083.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___104_5083.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___104_5083.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___104_5083.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___104_5083.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___104_5083.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___104_5083.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5084;
           FStar_TypeChecker_Env.lax_universes =
             (uu___104_5083.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___104_5083.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___104_5083.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___104_5083.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___104_5083.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____5086 = tc_modul env m in
       match uu____5086 with
       | (m,env) ->
           ((let uu____5094 =
               FStar_Options.dump_module
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
             match uu____5094 with
             | true  ->
                 let uu____5095 = FStar_Syntax_Print.modul_to_string m in
                 FStar_Util.print1 "%s\n" uu____5095
             | uu____5096 -> ());
            (let uu____5098 =
               (FStar_Options.dump_module
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             match uu____5098 with
             | true  ->
                 let normalize_toplevel_lets uu___82_5102 =
                   match uu___82_5102 with
                   | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
                       let n =
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
                         let uu____5129 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____5129 with
                         | (univnames,e) ->
                             let uu___105_5134 = lb in
                             let uu____5135 =
                               let uu____5138 =
                                 FStar_TypeChecker_Env.push_univ_vars env
                                   univnames in
                               n uu____5138 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___105_5134.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___105_5134.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___105_5134.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___105_5134.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____5135
                             } in
                       let uu____5139 =
                         let uu____5148 =
                           let uu____5152 = FStar_List.map update lbs in
                           (b, uu____5152) in
                         (uu____5148, r, ids, qs, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5139
                   | se -> se in
                 let normalized_module =
                   let uu___106_5163 = m in
                   let uu____5164 =
                     FStar_List.map normalize_toplevel_lets
                       m.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___106_5163.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____5164;
                     FStar_Syntax_Syntax.exports =
                       (uu___106_5163.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___106_5163.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____5165 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____5165
             | uu____5166 -> ());
            (m, env)))