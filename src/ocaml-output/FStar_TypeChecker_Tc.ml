open Prims
let set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for ()  in
      match uu____7 with
      | Some l ->
          let lid =
            let uu____11 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____11 l  in
          let uu___84_12 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___84_12.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___84_12.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___84_12.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___84_12.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___84_12.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___84_12.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___84_12.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___84_12.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___84_12.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___84_12.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___84_12.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___84_12.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___84_12.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___84_12.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___84_12.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___84_12.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___84_12.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___84_12.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___84_12.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___84_12.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___84_12.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___84_12.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___84_12.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____18 = FStar_TypeChecker_Env.current_module env  in
                let uu____19 =
                  let uu____20 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____20 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____18 uu____19
            | l::uu____22 -> l  in
          let uu___85_24 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___85_24.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___85_24.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___85_24.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___85_24.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___85_24.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___85_24.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___85_24.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___85_24.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___85_24.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___85_24.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___85_24.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___85_24.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___85_24.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___85_24.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___85_24.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___85_24.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___85_24.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___85_24.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___85_24.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___85_24.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___85_24.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___85_24.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___85_24.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
  
let log : FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____30 =
         let uu____31 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31  in
       Prims.op_Negation uu____30)
  
let tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____41 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____41 with
        | (t1,c,g) ->
            (FStar_ST.write t1.FStar_Syntax_Syntax.tk
               (Some
                  ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t1)
  
let recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____63 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____63
         then
           let uu____64 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____64
         else ());
        (let uu____66 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____66 with
         | (t',uu____71,uu____72) ->
             ((let uu____74 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____74
               then
                 let uu____75 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____75
               else ());
              t))
  
let check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____86 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____86
  
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k  in
  let uu____108 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1
     in
  ([], uu____108) 
let monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
          FStar_Syntax_Syntax.bv *
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____138 =
          let uu____139 =
            let uu____140 =
              let uu____143 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s
                 in
              (uu____143, (FStar_Ident.range_of_lid m))  in
            FStar_Errors.Error uu____140  in
          Prims.raise uu____139  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            let n1 = FStar_List.length bs1  in
            let uu____178 =
              if n1 < (Prims.parse_int "2")
              then ([], [])
              else FStar_Util.first_N (n1 - (Prims.parse_int "2")) bs1  in
            (match uu____178 with
             | (indices,bs2) ->
                 (match bs2 with
                  | (a,uu____245)::(wp,uu____247)::[] ->
                      (indices, a, (wp.FStar_Syntax_Syntax.sort))
                  | uu____259 -> fail ()))
        | uu____263 -> fail ()
  
let rec tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____326 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____326 with
      | (effect_params_un,signature_un,opening) ->
          let uu____333 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un  in
          (match uu____333 with
           | (effect_params,env,uu____339) ->
               let uu____340 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____340 with
                | (signature,uu____344) ->
                    let ed1 =
                      let uu___86_346 = ed  in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___86_346.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___86_346.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___86_346.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___86_346.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___86_346.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___86_346.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___86_346.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___86_346.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___86_346.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___86_346.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___86_346.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___86_346.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___86_346.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___86_346.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___86_346.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___86_346.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___86_346.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___86_346.FStar_Syntax_Syntax.actions)
                      }  in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____350 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts)
                               in
                            ([], t1)  in
                          let uu___87_368 = ed1  in
                          let uu____369 = op ed1.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____370 = op ed1.FStar_Syntax_Syntax.bind_wp
                             in
                          let uu____371 =
                            op ed1.FStar_Syntax_Syntax.if_then_else  in
                          let uu____372 = op ed1.FStar_Syntax_Syntax.ite_wp
                             in
                          let uu____373 = op ed1.FStar_Syntax_Syntax.stronger
                             in
                          let uu____374 = op ed1.FStar_Syntax_Syntax.close_wp
                             in
                          let uu____375 = op ed1.FStar_Syntax_Syntax.assert_p
                             in
                          let uu____376 = op ed1.FStar_Syntax_Syntax.assume_p
                             in
                          let uu____377 = op ed1.FStar_Syntax_Syntax.null_wp
                             in
                          let uu____378 = op ed1.FStar_Syntax_Syntax.trivial
                             in
                          let uu____379 =
                            let uu____380 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr))  in
                            Prims.snd uu____380  in
                          let uu____386 =
                            op ed1.FStar_Syntax_Syntax.return_repr  in
                          let uu____387 =
                            op ed1.FStar_Syntax_Syntax.bind_repr  in
                          let uu____388 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___88_391 = a  in
                                 let uu____392 =
                                   let uu____393 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn))
                                      in
                                   Prims.snd uu____393  in
                                 let uu____399 =
                                   let uu____400 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ))
                                      in
                                   Prims.snd uu____400  in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___88_391.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___88_391.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___88_391.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____392;
                                   FStar_Syntax_Syntax.action_typ = uu____399
                                 }) ed1.FStar_Syntax_Syntax.actions
                             in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___87_368.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___87_368.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___87_368.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___87_368.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___87_368.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___87_368.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____369;
                            FStar_Syntax_Syntax.bind_wp = uu____370;
                            FStar_Syntax_Syntax.if_then_else = uu____371;
                            FStar_Syntax_Syntax.ite_wp = uu____372;
                            FStar_Syntax_Syntax.stronger = uu____373;
                            FStar_Syntax_Syntax.close_wp = uu____374;
                            FStar_Syntax_Syntax.assert_p = uu____375;
                            FStar_Syntax_Syntax.assume_p = uu____376;
                            FStar_Syntax_Syntax.null_wp = uu____377;
                            FStar_Syntax_Syntax.trivial = uu____378;
                            FStar_Syntax_Syntax.repr = uu____379;
                            FStar_Syntax_Syntax.return_repr = uu____386;
                            FStar_Syntax_Syntax.bind_repr = uu____387;
                            FStar_Syntax_Syntax.actions = uu____388
                          }
                       in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____428 =
                          let uu____429 =
                            let uu____432 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t
                               in
                            (uu____432, (FStar_Ident.range_of_lid mname))  in
                          FStar_Errors.Error uu____429  in
                        Prims.raise uu____428  in
                      let uu____437 =
                        let uu____438 =
                          FStar_Syntax_Subst.compress signature1  in
                        uu____438.FStar_Syntax_Syntax.n  in
                      match uu____437 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs  in
                          (match bs1 with
                           | (a,uu____463)::(wp,uu____465)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____474 -> fail signature1)
                      | uu____475 -> fail signature1  in
                    let uu____476 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature
                       in
                    (match uu____476 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____494 =
                           let uu____495 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un
                              in
                           match uu____495 with
                           | (signature1,uu____503) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1
                            in
                         let env1 =
                           let uu____505 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature
                              in
                           FStar_TypeChecker_Env.push_bv env uu____505  in
                         ((let uu____507 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED")
                              in
                           if uu____507
                           then
                             let uu____508 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname
                                in
                             let uu____509 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders
                                in
                             let uu____510 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature
                                in
                             let uu____511 =
                               let uu____512 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               FStar_Syntax_Print.term_to_string uu____512
                                in
                             let uu____513 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort
                                in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____508 uu____509 uu____510 uu____511
                               uu____513
                           else ());
                          (let check_and_gen' env2 uu____526 k =
                             match uu____526 with
                             | (uu____531,t) -> check_and_gen env2 t k  in
                           let return_wp =
                             let expected_k =
                               let uu____537 =
                                 let uu____538 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____539 =
                                   let uu____541 =
                                     let uu____542 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____542
                                      in
                                   [uu____541]  in
                                 uu____538 :: uu____539  in
                               let uu____543 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a  in
                               FStar_Syntax_Util.arrow uu____537 uu____543
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k
                              in
                           let bind_wp =
                             let uu____545 = fresh_effect_signature ()  in
                             match uu____545 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____557 =
                                     let uu____558 =
                                       let uu____559 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____559
                                        in
                                     [uu____558]  in
                                   let uu____560 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____557
                                     uu____560
                                    in
                                 let expected_k =
                                   let uu____562 =
                                     let uu____563 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range
                                        in
                                     let uu____564 =
                                       let uu____566 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____567 =
                                         let uu____569 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____570 =
                                           let uu____572 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let uu____573 =
                                             let uu____575 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b
                                                in
                                             [uu____575]  in
                                           uu____572 :: uu____573  in
                                         uu____569 :: uu____570  in
                                       uu____566 :: uu____567  in
                                     uu____563 :: uu____564  in
                                   let uu____576 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____562
                                     uu____576
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k
                              in
                           let if_then_else1 =
                             let p =
                               let uu____579 =
                                 let uu____580 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____580 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____579
                                in
                             let expected_k =
                               let uu____586 =
                                 let uu____587 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____588 =
                                   let uu____590 =
                                     FStar_Syntax_Syntax.mk_binder p  in
                                   let uu____591 =
                                     let uu____593 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     let uu____594 =
                                       let uu____596 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____596]  in
                                     uu____593 :: uu____594  in
                                   uu____590 :: uu____591  in
                                 uu____587 :: uu____588  in
                               let uu____597 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____586 uu____597
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k
                              in
                           let ite_wp =
                             let expected_k =
                               let uu____600 =
                                 let uu____601 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____602 =
                                   let uu____604 =
                                     FStar_Syntax_Syntax.null_binder wp_a  in
                                   [uu____604]  in
                                 uu____601 :: uu____602  in
                               let uu____605 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____600 uu____605
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k
                              in
                           let stronger =
                             let uu____607 = FStar_Syntax_Util.type_u ()  in
                             match uu____607 with
                             | (t,uu____611) ->
                                 let expected_k =
                                   let uu____613 =
                                     let uu____614 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____615 =
                                       let uu____617 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       let uu____618 =
                                         let uu____620 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [uu____620]  in
                                       uu____617 :: uu____618  in
                                     uu____614 :: uu____615  in
                                   let uu____621 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   FStar_Syntax_Util.arrow uu____613
                                     uu____621
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k
                              in
                           let close_wp =
                             let b =
                               let uu____624 =
                                 let uu____625 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____625 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____624
                                in
                             let b_wp_a =
                               let uu____631 =
                                 let uu____632 =
                                   let uu____633 =
                                     FStar_Syntax_Syntax.bv_to_name b  in
                                   FStar_Syntax_Syntax.null_binder uu____633
                                    in
                                 [uu____632]  in
                               let uu____634 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____631 uu____634
                                in
                             let expected_k =
                               let uu____636 =
                                 let uu____637 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____638 =
                                   let uu____640 =
                                     FStar_Syntax_Syntax.mk_binder b  in
                                   let uu____641 =
                                     let uu____643 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a
                                        in
                                     [uu____643]  in
                                   uu____640 :: uu____641  in
                                 uu____637 :: uu____638  in
                               let uu____644 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____636 uu____644
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k
                              in
                           let assert_p =
                             let expected_k =
                               let uu____647 =
                                 let uu____648 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____649 =
                                   let uu____651 =
                                     let uu____652 =
                                       let uu____653 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____653
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____652
                                      in
                                   let uu____658 =
                                     let uu____660 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____660]  in
                                   uu____651 :: uu____658  in
                                 uu____648 :: uu____649  in
                               let uu____661 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____647 uu____661
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k
                              in
                           let assume_p =
                             let expected_k =
                               let uu____664 =
                                 let uu____665 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____666 =
                                   let uu____668 =
                                     let uu____669 =
                                       let uu____670 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____670
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____669
                                      in
                                   let uu____675 =
                                     let uu____677 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____677]  in
                                   uu____668 :: uu____675  in
                                 uu____665 :: uu____666  in
                               let uu____678 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____664 uu____678
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k
                              in
                           let null_wp =
                             let expected_k =
                               let uu____681 =
                                 let uu____682 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 [uu____682]  in
                               let uu____683 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____681 uu____683
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k
                              in
                           let trivial_wp =
                             let uu____685 = FStar_Syntax_Util.type_u ()  in
                             match uu____685 with
                             | (t,uu____689) ->
                                 let expected_k =
                                   let uu____691 =
                                     let uu____692 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____693 =
                                       let uu____695 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____695]  in
                                     uu____692 :: uu____693  in
                                   let uu____696 =
                                     FStar_Syntax_Syntax.mk_GTotal t  in
                                   FStar_Syntax_Util.arrow uu____691
                                     uu____696
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k
                              in
                           let uu____697 =
                             let uu____703 =
                               let uu____704 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr
                                  in
                               uu____704.FStar_Syntax_Syntax.n  in
                             match uu____703 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____713 ->
                                 let repr =
                                   let uu____715 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____715 with
                                   | (t,uu____719) ->
                                       let expected_k =
                                         let uu____721 =
                                           let uu____722 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____723 =
                                             let uu____725 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____725]  in
                                           uu____722 :: uu____723  in
                                         let uu____726 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow uu____721
                                           uu____726
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
                                   let uu____737 =
                                     let uu____740 =
                                       let uu____741 =
                                         let uu____751 =
                                           let uu____753 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____754 =
                                             let uu____756 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____756]  in
                                           uu____753 :: uu____754  in
                                         (repr1, uu____751)  in
                                       FStar_Syntax_Syntax.Tm_app uu____741
                                        in
                                     FStar_Syntax_Syntax.mk uu____740  in
                                   uu____737 None FStar_Range.dummyRange  in
                                 let mk_repr a1 wp =
                                   let uu____775 =
                                     FStar_Syntax_Syntax.bv_to_name a1  in
                                   mk_repr' uu____775 wp  in
                                 let destruct_repr t =
                                   let uu____786 =
                                     let uu____787 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____787.FStar_Syntax_Syntax.n  in
                                   match uu____786 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____796,(t1,uu____798)::(wp,uu____800)::[])
                                       -> (t1, wp)
                                   | uu____834 ->
                                       failwith "Unexpected repr type"
                                    in
                                 let bind_repr =
                                   let r =
                                     let uu____843 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_All.pipe_right uu____843
                                       FStar_Syntax_Syntax.fv_to_tm
                                      in
                                   let uu____844 = fresh_effect_signature ()
                                      in
                                   match uu____844 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____856 =
                                           let uu____857 =
                                             let uu____858 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____858
                                              in
                                           [uu____857]  in
                                         let uu____859 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____856
                                           uu____859
                                          in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a
                                          in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b
                                          in
                                       let x_a =
                                         let uu____863 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____863
                                          in
                                       let wp_g_x =
                                         let uu____867 =
                                           let uu____868 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g
                                              in
                                           let uu____869 =
                                             let uu____870 =
                                               let uu____871 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____871
                                                in
                                             [uu____870]  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____868 uu____869
                                            in
                                         uu____867 None
                                           FStar_Range.dummyRange
                                          in
                                       let res =
                                         let wp =
                                           let uu____882 =
                                             let uu____883 =
                                               let uu____884 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp
                                                  in
                                               FStar_All.pipe_right uu____884
                                                 Prims.snd
                                                in
                                             let uu____889 =
                                               let uu____890 =
                                                 let uu____892 =
                                                   let uu____894 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   let uu____895 =
                                                     let uu____897 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b
                                                        in
                                                     let uu____898 =
                                                       let uu____900 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f
                                                          in
                                                       let uu____901 =
                                                         let uu____903 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g
                                                            in
                                                         [uu____903]  in
                                                       uu____900 :: uu____901
                                                        in
                                                     uu____897 :: uu____898
                                                      in
                                                   uu____894 :: uu____895  in
                                                 r :: uu____892  in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____890
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____883 uu____889
                                              in
                                           uu____882 None
                                             FStar_Range.dummyRange
                                            in
                                         mk_repr b wp  in
                                       let expected_k =
                                         let uu____909 =
                                           let uu____910 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____911 =
                                             let uu____913 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b
                                                in
                                             let uu____914 =
                                               let uu____916 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f
                                                  in
                                               let uu____917 =
                                                 let uu____919 =
                                                   let uu____920 =
                                                     let uu____921 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f
                                                        in
                                                     mk_repr a uu____921  in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____920
                                                    in
                                                 let uu____922 =
                                                   let uu____924 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g
                                                      in
                                                   let uu____925 =
                                                     let uu____927 =
                                                       let uu____928 =
                                                         let uu____929 =
                                                           let uu____930 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a
                                                              in
                                                           [uu____930]  in
                                                         let uu____931 =
                                                           let uu____932 =
                                                             mk_repr b wp_g_x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____932
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           uu____929
                                                           uu____931
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____928
                                                        in
                                                     [uu____927]  in
                                                   uu____924 :: uu____925  in
                                                 uu____919 :: uu____922  in
                                               uu____916 :: uu____917  in
                                             uu____913 :: uu____914  in
                                           uu____910 :: uu____911  in
                                         let uu____933 =
                                           FStar_Syntax_Syntax.mk_Total res
                                            in
                                         FStar_Syntax_Util.arrow uu____909
                                           uu____933
                                          in
                                       let uu____934 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k
                                          in
                                       (match uu____934 with
                                        | (expected_k1,uu____939,uu____940)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let env3 =
                                              let uu___89_944 = env2  in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___89_944.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___89_944.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___89_944.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___89_944.FStar_TypeChecker_Env.qname_and_index)
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
                                     let uu____951 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____951
                                      in
                                   let res =
                                     let wp =
                                       let uu____958 =
                                         let uu____959 =
                                           let uu____960 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp
                                              in
                                           FStar_All.pipe_right uu____960
                                             Prims.snd
                                            in
                                         let uu____965 =
                                           let uu____966 =
                                             let uu____968 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             let uu____969 =
                                               let uu____971 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               [uu____971]  in
                                             uu____968 :: uu____969  in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____966
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____959 uu____965
                                          in
                                       uu____958 None FStar_Range.dummyRange
                                        in
                                     mk_repr a wp  in
                                   let expected_k =
                                     let uu____977 =
                                       let uu____978 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____979 =
                                         let uu____981 =
                                           FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                         [uu____981]  in
                                       uu____978 :: uu____979  in
                                     let uu____982 =
                                       FStar_Syntax_Syntax.mk_Total res  in
                                     FStar_Syntax_Util.arrow uu____977
                                       uu____982
                                      in
                                   let uu____983 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k
                                      in
                                   match uu____983 with
                                   | (expected_k1,uu____991,uu____992) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (Prims.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                          in
                                       let uu____995 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1
                                          in
                                       (match uu____995 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1007 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos)))))
                                    in
                                 let actions =
                                   let check_action act =
                                     let uu____1018 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ
                                        in
                                     match uu____1018 with
                                     | (act_typ,uu____1023,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env1 act_typ
                                            in
                                         ((let uu____1027 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED")
                                              in
                                           if uu____1027
                                           then
                                             let uu____1028 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn
                                                in
                                             let uu____1029 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ
                                                in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1028 uu____1029
                                           else ());
                                          (let uu____1031 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn
                                              in
                                           match uu____1031 with
                                           | (act_defn,uu____1036,g_a) ->
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
                                               let uu____1040 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1
                                                    in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1058 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____1058 with
                                                      | (bs1,uu____1064) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let k =
                                                            let uu____1069 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1069
                                                             in
                                                          let uu____1070 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k
                                                             in
                                                          (match uu____1070
                                                           with
                                                           | (k1,uu____1077,g)
                                                               -> (k1, g)))
                                                 | uu____1079 ->
                                                     let uu____1080 =
                                                       let uu____1081 =
                                                         let uu____1084 =
                                                           let uu____1085 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2
                                                              in
                                                           let uu____1086 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2
                                                              in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1085
                                                             uu____1086
                                                            in
                                                         (uu____1084,
                                                           (act_defn1.FStar_Syntax_Syntax.pos))
                                                          in
                                                       FStar_Errors.Error
                                                         uu____1081
                                                        in
                                                     Prims.raise uu____1080
                                                  in
                                               (match uu____1040 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k
                                                       in
                                                    ((let uu____1093 =
                                                        let uu____1094 =
                                                          let uu____1095 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g
                                                             in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1095
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1094
                                                         in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1093);
                                                     (let act_typ2 =
                                                        let uu____1097 =
                                                          let uu____1098 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k
                                                             in
                                                          uu____1098.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____1097 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1113 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____1113
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1118
                                                                   =
                                                                   let uu____1125
                                                                    =
                                                                    FStar_TypeChecker_Env.result_typ
                                                                    env1 c1
                                                                     in
                                                                   destruct_repr
                                                                    uu____1125
                                                                    in
                                                                 (match uu____1118
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1137
                                                                    =
                                                                    let uu____1138
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1138]
                                                                     in
                                                                    let uu____1139
                                                                    =
                                                                    let uu____1145
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    a1  in
                                                                    let uu____1146
                                                                    =
                                                                    let uu____1148
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1148]
                                                                     in
                                                                    uu____1145
                                                                    ::
                                                                    uu____1146
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1137;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1139;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1149
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1149))
                                                        | uu____1150 ->
                                                            failwith ""
                                                         in
                                                      let uu____1151 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1
                                                         in
                                                      match uu____1151 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2
                                                             in
                                                          let uu___90_1157 =
                                                            act  in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___90_1157.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___90_1157.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          })))))
                                      in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action)
                                    in
                                 (repr, bind_repr, return_repr, actions)
                              in
                           match uu____697 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1171 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature
                                    in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1171
                                  in
                               let uu____1172 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t
                                  in
                               (match uu____1172 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1178 =
                                        let uu____1181 =
                                          let uu____1182 =
                                            FStar_Syntax_Subst.compress t1
                                             in
                                          uu____1182.FStar_Syntax_Syntax.n
                                           in
                                        (effect_params, uu____1181)  in
                                      match uu____1178 with
                                      | ([],uu____1185) -> t1
                                      | (uu____1191,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1192,c)) ->
                                          FStar_TypeChecker_Env.result_typ
                                            env0 c
                                      | uu____1204 -> failwith "Impossible"
                                       in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1215 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts
                                           in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1215
                                         in
                                      let m =
                                        FStar_List.length (Prims.fst ts1)  in
                                      (let uu____1220 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1221 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1)
                                                in
                                             Prims.op_Negation uu____1221))
                                           && (m <> n1)
                                          in
                                       if uu____1220
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic"
                                            in
                                         let uu____1230 =
                                           let uu____1231 =
                                             FStar_Util.string_of_int n1  in
                                           let uu____1232 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1
                                              in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1231 uu____1232
                                            in
                                         failwith uu____1230
                                       else ());
                                      ts1  in
                                    let close_action act =
                                      let uu____1238 =
                                        close1 (~- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn))
                                         in
                                      match uu____1238 with
                                      | (univs2,defn) ->
                                          let uu____1243 =
                                            close1 (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ))
                                             in
                                          (match uu____1243 with
                                           | (univs',typ) ->
                                               let uu___91_1249 = act  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___91_1249.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___91_1249.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               })
                                       in
                                    let nunivs = FStar_List.length univs1  in
                                    let ed3 =
                                      let uu___92_1254 = ed2  in
                                      let uu____1255 =
                                        close1 (Prims.parse_int "0")
                                          return_wp
                                         in
                                      let uu____1256 =
                                        close1 (Prims.parse_int "1") bind_wp
                                         in
                                      let uu____1257 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1
                                         in
                                      let uu____1258 =
                                        close1 (Prims.parse_int "0") ite_wp
                                         in
                                      let uu____1259 =
                                        close1 (Prims.parse_int "0") stronger
                                         in
                                      let uu____1260 =
                                        close1 (Prims.parse_int "1") close_wp
                                         in
                                      let uu____1261 =
                                        close1 (Prims.parse_int "0") assert_p
                                         in
                                      let uu____1262 =
                                        close1 (Prims.parse_int "0") assume_p
                                         in
                                      let uu____1263 =
                                        close1 (Prims.parse_int "0") null_wp
                                         in
                                      let uu____1264 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp
                                         in
                                      let uu____1265 =
                                        let uu____1266 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr)
                                           in
                                        Prims.snd uu____1266  in
                                      let uu____1272 =
                                        close1 (Prims.parse_int "0")
                                          return_repr
                                         in
                                      let uu____1273 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr
                                         in
                                      let uu____1274 =
                                        FStar_List.map close_action actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___92_1254.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___92_1254.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___92_1254.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1255;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1256;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1257;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1258;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1259;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1260;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1261;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1262;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1263;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1264;
                                        FStar_Syntax_Syntax.repr = uu____1265;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1272;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1273;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1274
                                      }  in
                                    ((let uu____1277 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED"))
                                         in
                                      if uu____1277
                                      then
                                        let uu____1278 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print_string uu____1278
                                      else ());
                                     ed3)))))))

and cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt Prims.option)
  =
  fun env  ->
    fun ed  ->
      let uu____1282 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1282 with
      | (effect_binders_un,signature_un) ->
          let uu____1292 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1292 with
           | (effect_binders,env1,uu____1303) ->
               let uu____1304 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1304 with
                | (signature,uu____1313) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1322  ->
                           match uu____1322 with
                           | (bv,qual) ->
                               let uu____1329 =
                                 let uu___93_1330 = bv  in
                                 let uu____1331 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___93_1330.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___93_1330.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1331
                                 }  in
                               (uu____1329, qual)) effect_binders
                       in
                    let uu____1334 =
                      let uu____1339 =
                        let uu____1340 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____1340.FStar_Syntax_Syntax.n  in
                      match uu____1339 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1348)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1363 ->
                          failwith "bad shape for effect-for-free signature"
                       in
                    (match uu____1334 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1380 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____1380
                           then
                             let uu____1381 =
                               let uu____1383 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               Some uu____1383  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1381
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders1
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____1393 =
                             FStar_TypeChecker_TcTerm.tc_term env1 t1  in
                           match uu____1393 with
                           | (t2,comp,uu____1401) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____1412 =
                           open_and_check ed.FStar_Syntax_Syntax.repr  in
                         (match uu____1412 with
                          | (repr,_comp) ->
                              ((let uu____1423 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____1423
                                then
                                  let uu____1424 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1424
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let wp_type1 = recheck_debug "*" env1 wp_type
                                   in
                                let wp_a =
                                  let uu____1430 =
                                    let uu____1431 =
                                      let uu____1432 =
                                        let uu____1442 =
                                          let uu____1446 =
                                            let uu____1449 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____1450 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____1449, uu____1450)  in
                                          [uu____1446]  in
                                        (wp_type1, uu____1442)  in
                                      FStar_Syntax_Syntax.Tm_app uu____1432
                                       in
                                    mk1 uu____1431  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1430
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____1465 =
                                      let uu____1468 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____1468)  in
                                    let uu____1469 =
                                      let uu____1473 =
                                        let uu____1474 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a
                                           in
                                        FStar_All.pipe_right uu____1474
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____1473]  in
                                    uu____1465 :: uu____1469  in
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
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       (Prims.strcat
                                          (FStar_Ident.text_of_lid
                                             ed.FStar_Syntax_Syntax.mname)
                                          (Prims.strcat "_" name)))
                                    FStar_Range.dummyRange
                                   in
                                let elaborate_and_star dmff_env1 item =
                                  let uu____1507 = item  in
                                  match uu____1507 with
                                  | (u_item,item1) ->
                                      let uu____1519 = open_and_check item1
                                         in
                                      (match uu____1519 with
                                       | (item2,item_comp) ->
                                           ((let uu____1529 =
                                               let uu____1530 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____1530
                                                in
                                             if uu____1529
                                             then
                                               let uu____1531 =
                                                 let uu____1532 =
                                                   let uu____1533 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____1534 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1533 uu____1534
                                                    in
                                                 FStar_Errors.Err uu____1532
                                                  in
                                               Prims.raise uu____1531
                                             else ());
                                            (let uu____1536 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____1536 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env1
                                                     item_wp
                                                    in
                                                 let item_elab1 =
                                                   recheck_debug "_" env1
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1))))
                                   in
                                let uu____1549 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____1549 with
                                | (dmff_env1,uu____1560,bind_wp,bind_elab) ->
                                    let uu____1563 =
                                      elaborate_and_star dmff_env1
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____1563 with
                                     | (dmff_env2,uu____1574,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1578 =
                                             let uu____1579 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1579.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1578 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1617 =
                                                 let uu____1625 =
                                                   let uu____1628 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1628
                                                    in
                                                 match uu____1625 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1667 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____1617 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1689 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1689 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let uu____1697 =
                                                        let uu____1698 =
                                                          let uu____1699 =
                                                            let uu____1709 =
                                                              let uu____1713
                                                                =
                                                                let uu____1716
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11)
                                                                   in
                                                                let uu____1717
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____1716,
                                                                  uu____1717)
                                                                 in
                                                              [uu____1713]
                                                               in
                                                            (wp_type1,
                                                              uu____1709)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1699
                                                           in
                                                        mk1 uu____1698  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 uu____1697
                                                       in
                                                    let uu____1725 =
                                                      let uu____1735 =
                                                        let uu____1736 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1736
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1735
                                                       in
                                                    (match uu____1725 with
                                                     | (bs1,body2,what') ->
                                                         let t2 =
                                                           (Prims.fst b21).FStar_Syntax_Syntax.sort
                                                            in
                                                         let pure_wp_type =
                                                           FStar_TypeChecker_DMFF.double_star
                                                             t2
                                                            in
                                                         let wp =
                                                           FStar_Syntax_Syntax.gen_bv
                                                             "wp" None
                                                             pure_wp_type
                                                            in
                                                         let body3 =
                                                           let uu____1769 =
                                                             let uu____1770 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp
                                                                in
                                                             let uu____1771 =
                                                               let uu____1772
                                                                 =
                                                                 let uu____1776
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'
                                                                    in
                                                                 (uu____1776,
                                                                   None)
                                                                  in
                                                               [uu____1772]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____1770
                                                               uu____1771
                                                              in
                                                           uu____1769 None
                                                             FStar_Range.dummyRange
                                                            in
                                                         let uu____1792 =
                                                           let uu____1796 =
                                                             let uu____1800 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp
                                                                in
                                                             [uu____1800]  in
                                                           b11 :: uu____1796
                                                            in
                                                         let uu____1803 =
                                                           FStar_Syntax_Util.abs
                                                             bs1 body3 what
                                                            in
                                                         FStar_Syntax_Util.abs
                                                           uu____1792
                                                           uu____1803
                                                           (Some
                                                              (FStar_Util.Inr
                                                                 (FStar_Syntax_Const.effect_GTot_lid,
                                                                   [])))))
                                           | uu____1813 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let return_wp1 =
                                           let uu____1815 =
                                             let uu____1816 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1816.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1815 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1854 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1854
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1870 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let bind_wp1 =
                                           let uu____1872 =
                                             let uu____1873 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____1873.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1872 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None
                                                  in
                                               let uu____1902 =
                                                 let uu____1906 =
                                                   let uu____1908 =
                                                     let uu____1909 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____1909
                                                      in
                                                   [uu____1908]  in
                                                 FStar_List.append uu____1906
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____1902 body what
                                           | uu____1910 ->
                                               failwith
                                                 "unexpected shape for bind"
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____1928 =
                                                let uu____1929 =
                                                  let uu____1930 =
                                                    let uu____1940 =
                                                      let uu____1941 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      Prims.snd uu____1941
                                                       in
                                                    (t, uu____1940)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____1930
                                                   in
                                                mk1 uu____1929  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____1928)
                                            in
                                         let register name item =
                                           let uu____1953 =
                                             let uu____1956 = mk_lid name  in
                                             let uu____1957 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item None
                                                in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____1956 uu____1957
                                              in
                                           match uu____1953 with
                                           | (sigelt,fv) ->
                                               ((let uu____1966 =
                                                   let uu____1968 =
                                                     FStar_ST.read sigelts
                                                      in
                                                   sigelt :: uu____1968  in
                                                 FStar_ST.write sigelts
                                                   uu____1966);
                                                fv)
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____1979 =
                                             let uu____1981 =
                                               FStar_ST.read sigelts  in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____1981
                                              in
                                           FStar_ST.write sigelts uu____1979);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____1991 =
                                              let uu____1993 =
                                                FStar_ST.read sigelts  in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: uu____1993
                                               in
                                            FStar_ST.write sigelts uu____1991);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____2003 =
                                               let uu____2005 =
                                                 FStar_ST.read sigelts  in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: uu____2005
                                                in
                                             FStar_ST.write sigelts
                                               uu____2003);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____2015 =
                                                let uu____2017 =
                                                  FStar_ST.read sigelts  in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: uu____2017
                                                 in
                                              FStar_ST.write sigelts
                                                uu____2015);
                                             (let uu____2025 =
                                                FStar_List.fold_left
                                                  (fun uu____2032  ->
                                                     fun action  ->
                                                       match uu____2032 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let uu____2044 =
                                                             elaborate_and_star
                                                               dmff_env3
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn))
                                                              in
                                                           (match uu____2044
                                                            with
                                                            | (dmff_env4,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                   in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env4
                                                                    action_t
                                                                    action_wp
                                                                   in
                                                                let action_elab1
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab
                                                                   in
                                                                let action_typ_with_wp1
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp
                                                                   in
                                                                let uu____2060
                                                                  =
                                                                  let uu____2062
                                                                    =
                                                                    let uu___94_2063
                                                                    = action
                                                                     in
                                                                    let uu____2064
                                                                    =
                                                                    apply_close
                                                                    action_elab1
                                                                     in
                                                                    let uu____2065
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___94_2063.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___94_2063.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___94_2063.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2064;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2065
                                                                    }  in
                                                                  uu____2062
                                                                    ::
                                                                    actions
                                                                   in
                                                                (dmff_env4,
                                                                  uu____2060)))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____2025 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a
                                                       in
                                                    let binders =
                                                      let uu____2083 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____2084 =
                                                        let uu____2086 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____2086]  in
                                                      uu____2083 ::
                                                        uu____2084
                                                       in
                                                    let uu____2087 =
                                                      let uu____2088 =
                                                        let uu____2089 =
                                                          let uu____2090 =
                                                            let uu____2100 =
                                                              let uu____2104
                                                                =
                                                                let uu____2107
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____2108
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2107,
                                                                  uu____2108)
                                                                 in
                                                              [uu____2104]
                                                               in
                                                            (repr,
                                                              uu____2100)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2090
                                                           in
                                                        mk1 uu____2089  in
                                                      let uu____2116 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2088
                                                        uu____2116
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2087 None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____2124 =
                                                    let uu____2127 =
                                                      let uu____2128 =
                                                        let uu____2131 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2131
                                                         in
                                                      uu____2128.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2127 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2137)
                                                        ->
                                                        let uu____2164 =
                                                          let uu____2173 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____2173
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2204 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____2164
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2230 =
                                                               let uu____2231
                                                                 =
                                                                 let uu____2234
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2234
                                                                  in
                                                               uu____2231.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____2230
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2249
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____2249
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2256
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2267
                                                                     ->
                                                                    match uu____2267
                                                                    with
                                                                    | 
                                                                    (bv,uu____2271)
                                                                    ->
                                                                    let uu____2272
                                                                    =
                                                                    let uu____2273
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2273
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2272
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2256
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
                                                                    uu____2304
                                                                    ->
                                                                    let uu____2308
                                                                    =
                                                                    let uu____2309
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2309
                                                                     in
                                                                    failwith
                                                                    uu____2308
                                                                     in
                                                                    let uu____2312
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2313
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None  in
                                                                    (uu____2312,
                                                                    uu____2313)))
                                                              | uu____2321 ->
                                                                  let uu____2322
                                                                    =
                                                                    let uu____2323
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2323
                                                                     in
                                                                  failwith
                                                                    uu____2322))
                                                    | uu____2326 ->
                                                        let uu____2327 =
                                                          let uu____2328 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1
                                                             in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2328
                                                           in
                                                        failwith uu____2327
                                                     in
                                                  (match uu____2124 with
                                                   | (pre,post) ->
                                                       ((let uu____2339 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____2341 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____2343 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___95_2345 =
                                                             ed  in
                                                           let uu____2346 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____2347 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____2348 =
                                                             let uu____2349 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____2349)
                                                              in
                                                           let uu____2355 =
                                                             let uu____2356 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____2356)
                                                              in
                                                           let uu____2362 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____2363 =
                                                             let uu____2364 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____2364)
                                                              in
                                                           let uu____2370 =
                                                             let uu____2371 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____2371)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2346;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2347;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2348;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2355;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___95_2345.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2362;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2363;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2370;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____2377 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____2377
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2388
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____2388
                                                               then
                                                                 let uu____2389
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____2389
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let label_to_comp_typ
                                                                    l =
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    = l;
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = [];
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = [];
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____2407
                                                                    =
                                                                    let uu____2409
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    Some
                                                                    uu____2409
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.sub_eff_univs
                                                                    = [];
                                                                    FStar_Syntax_Syntax.sub_eff_binders
                                                                    = [];
                                                                    FStar_Syntax_Syntax.sub_eff_source
                                                                    =
                                                                    (label_to_comp_typ
                                                                    FStar_Syntax_Const.effect_PURE_lid);
                                                                    FStar_Syntax_Syntax.sub_eff_target
                                                                    =
                                                                    (label_to_comp_typ
                                                                    ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.sub_eff_lift_wp
                                                                    =
                                                                    uu____2407;
                                                                    FStar_Syntax_Syntax.sub_eff_lift
                                                                    = None
                                                                    }  in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None
                                                                  in
                                                               let uu____2417
                                                                 =
                                                                 let uu____2419
                                                                   =
                                                                   let uu____2421
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____2421
                                                                    in
                                                                 FStar_List.append
                                                                   uu____2419
                                                                   sigelts'
                                                                  in
                                                               (uu____2417,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))

and tc_lex_t :
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
              (lex_t1,[],[],t,uu____2444,uu____2445,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top1,[],_t_top,_lex_t_top,_0_28,[],uu____2450,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2455,r2))::[]
              when
              ((_0_28 = (Prims.parse_int "0")) &&
                 (_0_29 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top1
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r)  in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r
                 in
              let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
              let tc =
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t1, [u], [], t2, [],
                    [FStar_Syntax_Const.lextop_lid;
                    FStar_Syntax_Const.lexcons_lid], [], r)
                 in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1)  in
              let lex_top_t =
                let uu____2499 =
                  let uu____2502 =
                    let uu____2503 =
                      let uu____2508 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None
                         in
                      (uu____2508, [FStar_Syntax_Syntax.U_name utop])  in
                    FStar_Syntax_Syntax.Tm_uinst uu____2503  in
                  FStar_Syntax_Syntax.mk uu____2502  in
                uu____2499 None r1  in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top1, [utop], lex_top_t1,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r1)
                 in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let lex_cons_t =
                let a =
                  let uu____2527 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2527  in
                let hd1 =
                  let uu____2533 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2533  in
                let tl1 =
                  let uu____2535 =
                    let uu____2536 =
                      let uu____2539 =
                        let uu____2540 =
                          let uu____2545 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None
                             in
                          (uu____2545, [FStar_Syntax_Syntax.U_name ucons2])
                           in
                        FStar_Syntax_Syntax.Tm_uinst uu____2540  in
                      FStar_Syntax_Syntax.mk uu____2539  in
                    uu____2536 None r2  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2535  in
                let res =
                  let uu____2558 =
                    let uu____2561 =
                      let uu____2562 =
                        let uu____2567 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None
                           in
                        (uu____2567,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]])
                         in
                      FStar_Syntax_Syntax.Tm_uinst uu____2562  in
                    FStar_Syntax_Syntax.mk uu____2561  in
                  uu____2558 None r2  in
                let uu____2577 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2577
                 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t
                 in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t1,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r2)
                 in
              let uu____2598 =
                let uu____2606 = FStar_TypeChecker_Env.get_range env  in
                ([tc; dc_lextop; dc_lexcons], [], lids, uu____2606)  in
              FStar_Syntax_Syntax.Sig_bundle uu____2598
          | uu____2610 ->
              let uu____2612 =
                let uu____2613 =
                  FStar_Syntax_Print.sigelt_to_string
                    (FStar_Syntax_Syntax.Sig_bundle
                       (ses, [], lids, FStar_Range.dummyRange))
                   in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2613  in
              failwith uu____2612

and tc_assume :
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
            let env1 = FStar_TypeChecker_Env.set_range env r  in
            let uu____2624 = FStar_Syntax_Util.type_u ()  in
            match uu____2624 with
            | (k,uu____2628) ->
                let phi1 =
                  let uu____2630 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____2630
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi1, quals, r))

and tc_inductive :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env  in
          let uu____2641 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids
             in
          match uu____2641 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2660 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas
                   in
                FStar_All.pipe_right uu____2660 FStar_List.flatten  in
              ((let uu____2668 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____2668
                then ()
                else
                  (let env1 =
                     FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env1
                           in
                        if Prims.op_Negation b
                        then
                          let uu____2674 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2680,uu____2681,uu____2682,uu____2683,uu____2684,uu____2685,r)
                                -> (lid, r)
                            | uu____2693 -> failwith "Impossible!"  in
                          match uu____2674 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2702 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2706,uu____2707,uu____2708,uu____2709,uu____2710,uu____2711,uu____2712)
                        -> lid
                    | uu____2719 -> failwith "Impossible"  in
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
                let uu____2725 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____2725
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
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                      in
                   let uu____2741 =
                     let uu____2743 =
                       let uu____2744 =
                         let uu____2752 =
                           FStar_TypeChecker_Env.get_range env0  in
                         ((FStar_List.append tcs datas), quals, lids,
                           uu____2752)
                          in
                       FStar_Syntax_Syntax.Sig_bundle uu____2744  in
                     uu____2743 :: ses1  in
                   (uu____2741, data_ops_ses))))

and tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (match se with
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let se1 = tc_lex_t env2 ses quals lids  in
           let uu____2792 = FStar_TypeChecker_Env.push_sigelt env2 se1  in
           ([se1], uu____2792, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____2806 = tc_inductive env2 ses quals lids  in
           (match uu____2806 with
            | (ses1,projectors_ses) ->
                let env3 =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se1  -> FStar_TypeChecker_Env.push_sigelt env' se1)
                    env2 ses1
                   in
                (ses1, env3, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options1 t s =
             let uu____2836 = FStar_Options.set_options t s  in
             match uu____2836 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s1), r))
              in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], env1, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], env1, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____2854 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____2854 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env1, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____2862 = cps_and_elaborate env1 ne  in
           (match uu____2862 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [FStar_Syntax_Syntax.Sig_new_effect (ne1, r); lift]
                  | None  -> [FStar_Syntax_Syntax.Sig_new_effect (ne1, r)]
                   in
                ([], env1, (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne1 = tc_eff_decl env1 ne  in
           let se1 = FStar_Syntax_Syntax.Sig_new_effect (ne1, r)  in
           let env2 = FStar_TypeChecker_Env.push_sigelt env1 se1  in
           let uu____2891 =
             FStar_All.pipe_right ne1.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____2902  ->
                     fun a  ->
                       match uu____2902 with
                       | (env3,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne1.FStar_Syntax_Syntax.mname a
                              in
                           let uu____2915 =
                             FStar_TypeChecker_Env.push_sigelt env3 se_let
                              in
                           (uu____2915, (se_let :: ses))) (env2, [se1]))
              in
           (match uu____2891 with | (env3,ses) -> ([se1], env3, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub1,r) ->
           let source =
             (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
              in
           let target =
             (sub1.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
              in
           let ed_src = FStar_TypeChecker_Env.get_effect_decl env1 source  in
           let ed_tgt = FStar_TypeChecker_Env.get_effect_decl env1 target  in
           let uu____2935 =
             let uu____2944 =
               FStar_TypeChecker_Env.lookup_effect_lid env1 source  in
             monad_signature env1 source uu____2944  in
           (match uu____2935 with
            | (indices_a,a,wp_a_src) ->
                let uu____2963 =
                  let uu____2972 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1 target  in
                  monad_signature env1 target uu____2972  in
                (match uu____2963 with
                 | (indices_b,b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____2992 =
                         let uu____2994 =
                           let uu____2995 =
                             let uu____3000 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____3000)  in
                           FStar_Syntax_Syntax.NT uu____2995  in
                         [uu____2994]  in
                       FStar_Syntax_Subst.subst uu____2992 wp_b_tgt  in
                     let expected_k =
                       let uu____3002 =
                         let uu____3003 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____3004 =
                           let uu____3006 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____3006]  in
                         uu____3003 :: uu____3004  in
                       let uu____3007 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____3002 uu____3007  in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3026 =
                           let uu____3027 =
                             let uu____3030 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str
                                in
                             let uu____3031 =
                               FStar_TypeChecker_Env.get_range env1  in
                             (uu____3030, uu____3031)  in
                           FStar_Errors.Error uu____3027  in
                         Prims.raise uu____3026  in
                       let uu____3034 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name
                          in
                       match uu____3034 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____3041 =
                             let uu____3042 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable)
                                in
                             Prims.op_Negation uu____3042  in
                           if uu____3041
                           then no_reify eff_name
                           else
                             (let uu____3047 =
                                FStar_TypeChecker_Env.get_range env1  in
                              let uu____3048 =
                                let uu____3051 =
                                  let uu____3052 =
                                    let uu____3062 =
                                      let uu____3064 =
                                        FStar_Syntax_Syntax.as_arg a1  in
                                      let uu____3065 =
                                        let uu____3067 =
                                          FStar_Syntax_Syntax.as_arg wp  in
                                        [uu____3067]  in
                                      uu____3064 :: uu____3065  in
                                    (repr, uu____3062)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3052  in
                                FStar_Syntax_Syntax.mk uu____3051  in
                              uu____3048 None uu____3047)
                        in
                     let uu____3077 =
                       match ((sub1.FStar_Syntax_Syntax.sub_eff_lift),
                               (sub1.FStar_Syntax_Syntax.sub_eff_lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some lift_wp) ->
                           let uu____3096 =
                             tc_check_trivial_guard env1 lift_wp expected_k
                              in
                           (lift, uu____3096)
                       | (Some lift,None ) ->
                           let dmff_env =
                             FStar_TypeChecker_DMFF.empty env1
                               (FStar_TypeChecker_TcTerm.tc_constant
                                  FStar_Range.dummyRange)
                              in
                           let uu____3102 =
                             FStar_TypeChecker_DMFF.star_expr dmff_env lift
                              in
                           (match uu____3102 with
                            | (uu____3109,lift_wp,lift_elab) ->
                                let uu____3112 =
                                  recheck_debug "lift-wp" env1 lift_wp  in
                                let uu____3113 =
                                  recheck_debug "lift-elab" env1 lift_elab
                                   in
                                ((Some lift_elab), lift_wp))
                        in
                     (match uu____3077 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax  in
                          let env2 =
                            let uu___96_3126 = env1  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___96_3126.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___96_3126.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___96_3126.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___96_3126.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___96_3126.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___96_3126.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___96_3126.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___96_3126.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___96_3126.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___96_3126.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___96_3126.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___96_3126.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___96_3126.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___96_3126.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___96_3126.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___96_3126.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___96_3126.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___96_3126.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___96_3126.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___96_3126.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___96_3126.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___96_3126.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___96_3126.FStar_TypeChecker_Env.qname_and_index)
                            }  in
                          let lift1 =
                            match lift with
                            | None  -> None
                            | Some lift1 ->
                                let source1 =
                                  (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
                                   in
                                let uu____3132 =
                                  let uu____3141 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 source1
                                     in
                                  monad_signature env2 source1 uu____3141  in
                                (match uu____3132 with
                                 | (indices_a1,a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src1
                                        in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1  in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a
                                        in
                                     let repr_f =
                                       repr_type source1 a_typ wp_a_typ  in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2 lift_wp
                                          in
                                       let lift_wp_a =
                                         let uu____3169 =
                                           FStar_TypeChecker_Env.get_range
                                             env2
                                            in
                                         let uu____3170 =
                                           let uu____3173 =
                                             let uu____3174 =
                                               let uu____3184 =
                                                 let uu____3186 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ
                                                    in
                                                 let uu____3187 =
                                                   let uu____3189 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ
                                                      in
                                                   [uu____3189]  in
                                                 uu____3186 :: uu____3187  in
                                               (lift_wp1, uu____3184)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3174
                                              in
                                           FStar_Syntax_Syntax.mk uu____3173
                                            in
                                         uu____3170 None uu____3169  in
                                       let target1 =
                                         (sub1.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
                                          in
                                       repr_type target1 a_typ lift_wp_a  in
                                     let expected_k1 =
                                       let uu____3201 =
                                         let uu____3202 =
                                           FStar_Syntax_Syntax.mk_binder a1
                                            in
                                         let uu____3203 =
                                           let uu____3205 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let uu____3206 =
                                             let uu____3208 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [uu____3208]  in
                                           uu____3205 :: uu____3206  in
                                         uu____3202 :: uu____3203  in
                                       let uu____3209 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow uu____3201
                                         uu____3209
                                        in
                                     let uu____3210 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1
                                        in
                                     (match uu____3210 with
                                      | (expected_k2,uu____3216,uu____3217)
                                          ->
                                          let lift2 =
                                            tc_check_trivial_guard env2 lift1
                                              expected_k2
                                             in
                                          Some lift2))
                             in
                          let env3 =
                            let uu___97_3220 = env2  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___97_3220.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___97_3220.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___97_3220.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___97_3220.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___97_3220.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___97_3220.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___97_3220.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___97_3220.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___97_3220.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___97_3220.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___97_3220.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___97_3220.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___97_3220.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___97_3220.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___97_3220.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___97_3220.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___97_3220.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___97_3220.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax1;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___97_3220.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___97_3220.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___97_3220.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___97_3220.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___97_3220.FStar_TypeChecker_Env.qname_and_index)
                            }  in
                          let sub2 =
                            let uu___98_3222 = sub1  in
                            {
                              FStar_Syntax_Syntax.sub_eff_univs =
                                (uu___98_3222.FStar_Syntax_Syntax.sub_eff_univs);
                              FStar_Syntax_Syntax.sub_eff_binders =
                                (uu___98_3222.FStar_Syntax_Syntax.sub_eff_binders);
                              FStar_Syntax_Syntax.sub_eff_source =
                                (uu___98_3222.FStar_Syntax_Syntax.sub_eff_source);
                              FStar_Syntax_Syntax.sub_eff_target =
                                (uu___98_3222.FStar_Syntax_Syntax.sub_eff_target);
                              FStar_Syntax_Syntax.sub_eff_lift_wp =
                                (Some lift_wp);
                              FStar_Syntax_Syntax.sub_eff_lift = lift1
                            }  in
                          let se1 =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub2, r)  in
                          let env4 =
                            FStar_TypeChecker_Env.push_sigelt env3 se1  in
                          let env5 =
                            FStar_TypeChecker_Util.build_lattice env4 se1  in
                          ([se1], env5, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3242 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____3242 with
            | (tps1,c1) ->
                let uu____3252 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____3252 with
                 | (tps2,env3,us) ->
                     let uu____3264 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____3264 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____3279 =
                              let uu____3280 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3280
                               in
                            match uu____3279 with
                            | (uvs1,t) ->
                                let uu____3294 =
                                  let uu____3302 =
                                    let uu____3305 =
                                      let uu____3306 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____3306.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____3305)  in
                                  match uu____3302 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3316,c4)) -> ([], c4)
                                  | (uu____3340,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3358 -> failwith "Impossible"  in
                                (match uu____3294 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3388 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____3388 with
                                         | (uu____3391,t1) ->
                                             let uu____3393 =
                                               let uu____3394 =
                                                 let uu____3397 =
                                                   let uu____3398 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid
                                                      in
                                                   let uu____3399 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int
                                                      in
                                                   let uu____3402 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3398 uu____3399
                                                     uu____3402
                                                    in
                                                 (uu____3397, r)  in
                                               FStar_Errors.Error uu____3394
                                                in
                                             Prims.raise uu____3393)
                                      else ();
                                      (let se1 =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs1, tps4, c4, tags, flags,
                                             r)
                                          in
                                       let env4 =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se1
                                          in
                                       ([se1], env4, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___78_3432  ->
                   match uu___78_3432 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3433 -> false))
           -> ([], env1, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3444 =
             if uvs = []
             then
               let uu____3445 =
                 let uu____3446 = FStar_Syntax_Util.type_u ()  in
                 Prims.fst uu____3446  in
               check_and_gen env2 t uu____3445
             else
               (let uu____3450 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____3450 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3456 =
                        let uu____3457 = FStar_Syntax_Util.type_u ()  in
                        Prims.fst uu____3457  in
                      tc_check_trivial_guard env2 t1 uu____3456  in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2
                       in
                    let uu____3461 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                    (uvs1, uu____3461))
              in
           (match uu____3444 with
            | (uvs1,t1) ->
                let se1 =
                  FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uvs1, t1, quals, r)
                   in
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se1  in
                ([se1], env3, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se1 = tc_assume env1 lid phi quals r  in
           let env2 = FStar_TypeChecker_Env.push_sigelt env1 se1  in
           ([se1], env2, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit
              in
           let uu____3491 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____3491 with
            | (e1,c,g1) ->
                let uu____3503 =
                  let uu____3507 =
                    let uu____3509 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r
                       in
                    Some uu____3509  in
                  let uu____3510 =
                    let uu____3513 = c.FStar_Syntax_Syntax.lcomp_as_comp ()
                       in
                    (e1, uu____3513)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3507 uu____3510
                   in
                (match uu____3503 with
                 | (e2,uu____3524,g) ->
                     ((let uu____3527 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3527);
                      (let se1 = FStar_Syntax_Syntax.Sig_main (e2, r)  in
                       let env4 = FStar_TypeChecker_Env.push_sigelt env3 se1
                          in
                       ([se1], env4, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____3569 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____3569
                 then Some q
                 else
                   (let uu____3578 =
                      let uu____3579 =
                        let uu____3582 =
                          let uu____3583 = FStar_Syntax_Print.lid_to_string l
                             in
                          let uu____3584 =
                            FStar_Syntax_Print.quals_to_string q  in
                          let uu____3585 =
                            FStar_Syntax_Print.quals_to_string q'  in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3583 uu____3584 uu____3585
                           in
                        (uu____3582, r)  in
                      FStar_Errors.Error uu____3579  in
                    Prims.raise uu____3578)
              in
           let uu____3588 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3609  ->
                     fun lb  ->
                       match uu____3609 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3633 =
                             let uu____3639 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3639 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | Some ((uvs,tval),quals1) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals1
                                    in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____3691 ->
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let uu____3699 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef))
                                      in
                                   (false, uu____3699, quals_opt1)))
                              in
                           (match uu____3633 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [], (if quals = [] then None else Some quals)))
              in
           (match uu____3588 with
            | (should_generalize,lbs',quals_opt) ->
                let quals1 =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3753 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___79_3755  ->
                                match uu___79_3755 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3756 -> false))
                         in
                      if uu____3753
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3764 =
                    let uu____3767 =
                      let uu____3768 =
                        let uu____3776 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r
                           in
                        (((Prims.fst lbs), lbs'1), uu____3776)  in
                      FStar_Syntax_Syntax.Tm_let uu____3768  in
                    FStar_Syntax_Syntax.mk uu____3767  in
                  uu____3764 None r  in
                let uu____3798 =
                  let uu____3804 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___99_3808 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___99_3808.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___99_3808.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___99_3808.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___99_3808.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___99_3808.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___99_3808.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___99_3808.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___99_3808.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___99_3808.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___99_3808.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___99_3808.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___99_3808.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___99_3808.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___99_3808.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___99_3808.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___99_3808.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___99_3808.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___99_3808.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___99_3808.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___99_3808.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___99_3808.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___99_3808.FStar_TypeChecker_Env.qname_and_index)
                       }) e
                     in
                  match uu____3804 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3816;
                       FStar_Syntax_Syntax.pos = uu____3817;
                       FStar_Syntax_Syntax.vars = uu____3818;_},uu____3819,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals2 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3838,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals1
                        | uu____3843 -> quals1  in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs1, r, lids, quals2, attrs)), lbs1)
                  | uu____3853 -> failwith "impossible"  in
                (match uu____3798 with
                 | (se1,lbs1) ->
                     ((let uu____3876 = log env2  in
                       if uu____3876
                       then
                         let uu____3877 =
                           let uu____3878 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3885 =
                                         let uu____3890 =
                                           let uu____3891 =
                                             let uu____3896 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____3896.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____3891.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____3890
                                          in
                                       match uu____3885 with
                                       | None  -> true
                                       | uu____3903 -> false  in
                                     if should_log
                                     then
                                       let uu____3908 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____3909 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____3908 uu____3909
                                     else ""))
                              in
                           FStar_All.pipe_right uu____3878
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____3877
                       else ());
                      (let env3 = FStar_TypeChecker_Env.push_sigelt env2 se1
                          in
                       ([se1], env3, []))))))

let for_export :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___80_3939  ->
                match uu___80_3939 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____3940 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____3948 -> false  in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____3953 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3966,r) ->
          let uu____3974 = is_abstract quals  in
          if uu____3974
          then
            let for_export_bundle se1 uu____3993 =
              match uu____3993 with
              | (out,hidden1) ->
                  (match se1 with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4016,uu____4017,quals1,r1) ->
                       let dec =
                         let uu____4027 =
                           let uu____4034 =
                             let uu____4035 = FStar_Syntax_Syntax.mk_Total t
                                in
                             FStar_Syntax_Util.arrow bs uu____4035  in
                           (l, us, uu____4034,
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New :: quals1), r1)
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4027  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4042,uu____4043,uu____4044,uu____4045,r1)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r1)
                          in
                       ((dec :: out), (l :: hidden1))
                   | uu____4055 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4067,uu____4068,quals,uu____4070) ->
          let uu____4073 = is_abstract quals  in
          if uu____4073 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4090 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____4090
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____4100 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___81_4102  ->
                       match uu___81_4102 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4105 -> false))
                in
             if uu____4100 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4115 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4127,uu____4128,quals,uu____4130) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____4148 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____4148
          then ([], hidden)
          else
            (let dec =
               FStar_Syntax_Syntax.Sig_declare_typ
                 (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                   (lb.FStar_Syntax_Syntax.lbunivs),
                   (lb.FStar_Syntax_Syntax.lbtyp),
                   [FStar_Syntax_Syntax.Assumption],
                   (FStar_Ident.range_of_lid lid))
                in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4172) ->
          let uu____4179 = is_abstract quals  in
          if uu____4179
          then
            let uu____4184 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu____4190 =
                        let uu____4197 =
                          let uu____4198 =
                            let uu____4203 =
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                               in
                            uu____4203.FStar_Syntax_Syntax.fv_name  in
                          uu____4198.FStar_Syntax_Syntax.v  in
                        (uu____4197, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp),
                          (FStar_Syntax_Syntax.Assumption :: quals), r)
                         in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____4190))
               in
            (uu____4184, hidden)
          else ([se], hidden)
  
let tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4251 se =
        match uu____4251 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4281 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____4281
              then
                let uu____4282 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4282
              else ());
             (let uu____4284 = tc_decl env1 se  in
              match uu____4284 with
              | (ses',env2,ses_elaborated) ->
                  ((let uu____4308 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes"))
                       in
                    if uu____4308
                    then
                      let uu____4309 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4312 =
                                 let uu____4313 =
                                   FStar_Syntax_Print.sigelt_to_string se1
                                    in
                                 Prims.strcat uu____4313 "\n"  in
                               Prims.strcat s uu____4312) "" ses'
                         in
                      FStar_Util.print1 "Checked: %s\n" uu____4309
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4317 =
                      let accum_exports_hidden uu____4335 se1 =
                        match uu____4335 with
                        | (exports1,hidden1) ->
                            let uu____4351 = for_export hidden1 se1  in
                            (match uu____4351 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'
                       in
                    match uu____4317 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated)))))
         in
      let uu____4401 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses  in
      match uu____4401 with
      | (ses1,exports,env1,uu____4427) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env)
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
      (let uu____4452 = FStar_Options.debug_any ()  in
       if uu____4452
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
         let uu___100_4458 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___100_4458.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___100_4458.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___100_4458.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___100_4458.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___100_4458.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___100_4458.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___100_4458.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___100_4458.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___100_4458.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___100_4458.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___100_4458.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___100_4458.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___100_4458.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___100_4458.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___100_4458.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___100_4458.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___100_4458.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___100_4458.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___100_4458.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___100_4458.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___100_4458.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___100_4458.FStar_TypeChecker_Env.qname_and_index)
         }  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name
           in
        let uu____4461 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
           in
        match uu____4461 with
        | (ses,exports,env3) ->
            ((let uu___101_4479 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_4479.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___101_4479.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_4479.FStar_Syntax_Syntax.is_interface)
              }), exports, env3)))
  
let tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____4495 = tc_decls env decls  in
        match uu____4495 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___102_4513 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___102_4513.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___102_4513.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___102_4513.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___103_4527 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___103_4527.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___103_4527.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___103_4527.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___103_4527.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___103_4527.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___103_4527.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___103_4527.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___103_4527.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___103_4527.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___103_4527.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___103_4527.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___103_4527.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___103_4527.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___103_4527.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___103_4527.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___103_4527.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___103_4527.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___103_4527.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___103_4527.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___103_4527.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___103_4527.FStar_TypeChecker_Env.qname_and_index)
          }  in
        let check_term lid univs1 t =
          let uu____4538 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____4538 with
          | (univs2,t1) ->
              ((let uu____4544 =
                  let uu____4545 =
                    let uu____4548 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____4548  in
                  FStar_All.pipe_left uu____4545
                    (FStar_Options.Other "Exports")
                   in
                if uu____4544
                then
                  let uu____4549 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____4550 =
                    let uu____4551 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____4551
                      (FStar_String.concat ", ")
                     in
                  let uu____4556 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4549 uu____4550 uu____4556
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____4559 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____4559 Prims.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____4577 =
             let uu____4578 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____4579 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4578 uu____4579
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4577);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt uu___82_4584 =
          match uu___82_4584 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4587,uu____4588)
              ->
              let uu____4595 =
                let uu____4596 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4596  in
              if uu____4595
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4604,uu____4605,uu____4606,r) ->
              let t =
                let uu____4617 =
                  let uu____4620 =
                    let uu____4621 =
                      let uu____4629 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____4629)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____4621  in
                  FStar_Syntax_Syntax.mk uu____4620  in
                uu____4617 None r  in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4641,uu____4642,uu____4643,uu____4644,uu____4645)
              -> check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t,quals,uu____4654)
              ->
              let uu____4657 =
                let uu____4658 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4658  in
              if uu____4657 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4661,lbs),uu____4663,uu____4664,quals,uu____4666) ->
              let uu____4678 =
                let uu____4679 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4679  in
              if uu____4678
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
              (l,univs1,binders,comp,quals,flags,r) ->
              let uu____4700 =
                let uu____4701 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4701  in
              if uu____4700
              then
                let arrow1 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None r
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main _
            |FStar_Syntax_Syntax.Sig_assume _
             |FStar_Syntax_Syntax.Sig_new_effect _
              |FStar_Syntax_Syntax.Sig_new_effect_for_free _
               |FStar_Syntax_Syntax.Sig_sub_effect _
                |FStar_Syntax_Syntax.Sig_pragma _
              -> ()
           in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
  
let finish_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
          let uu___104_4734 = modul  in
          {
            FStar_Syntax_Syntax.name =
              (uu___104_4734.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___104_4734.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          }  in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
        (let uu____4737 =
           let uu____4738 = FStar_Options.lax ()  in
           Prims.op_Negation uu____4738  in
         if uu____4737 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____4744 =
           let uu____4745 = FStar_Options.interactive ()  in
           Prims.op_Negation uu____4745  in
         if uu____4744
         then
           let uu____4746 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_right uu____4746 Prims.ignore
         else ());
        (modul1, env1)
  
let tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4756 = tc_partial_modul env modul  in
      match uu____4756 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
  
let check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4777 = FStar_Options.debug_any ()  in
       if uu____4777
       then
         let uu____4778 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4778
       else ());
      (let env1 =
         let uu___105_4782 = env  in
         let uu____4783 =
           let uu____4784 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____4784  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___105_4782.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___105_4782.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___105_4782.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___105_4782.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___105_4782.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___105_4782.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___105_4782.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___105_4782.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___105_4782.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___105_4782.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___105_4782.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___105_4782.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___105_4782.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___105_4782.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___105_4782.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___105_4782.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___105_4782.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___105_4782.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4783;
           FStar_TypeChecker_Env.lax_universes =
             (uu___105_4782.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___105_4782.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___105_4782.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___105_4782.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___105_4782.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____4785 = tc_modul env1 m  in
       match uu____4785 with
       | (m1,env2) ->
           ((let uu____4793 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____4793
             then
               let uu____4794 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "%s\n" uu____4794
             else ());
            (let uu____4797 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____4797
             then
               let normalize_toplevel_lets uu___83_4801 =
                 match uu___83_4801 with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                        in
                     let update lb =
                       let uu____4828 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____4828 with
                       | (univnames1,e) ->
                           let uu___106_4833 = lb  in
                           let uu____4834 =
                             let uu____4837 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____4837 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___106_4833.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___106_4833.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___106_4833.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___106_4833.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4834
                           }
                        in
                     let uu____4838 =
                       let uu____4847 =
                         let uu____4851 = FStar_List.map update lbs  in
                         (b, uu____4851)  in
                       (uu____4847, r, ids, qs, attrs)  in
                     FStar_Syntax_Syntax.Sig_let uu____4838
                 | se -> se  in
               let normalized_module =
                 let uu___107_4862 = m1  in
                 let uu____4863 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___107_4862.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____4863;
                   FStar_Syntax_Syntax.exports =
                     (uu___107_4862.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___107_4862.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____4864 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____4864
             else ());
            (m1, env2)))
  