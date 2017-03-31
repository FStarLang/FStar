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
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____136 =
          let uu____137 =
            let uu____138 =
              let uu____141 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s
                 in
              (uu____141, (FStar_Ident.range_of_lid m))  in
            FStar_Errors.Error uu____138  in
          Prims.raise uu____137  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            let n1 = FStar_List.length bs1  in
            if n1 < (Prims.parse_int "2")
            then fail ()
            else
              (let uu____185 =
                 FStar_Util.first_N (n1 - (Prims.parse_int "1")) bs1  in
               match uu____185 with
               | (args,wp) ->
                   let uu____220 =
                     match wp with
                     | (wp1,uu____226)::[] -> wp1.FStar_Syntax_Syntax.sort
                     | uu____231 -> failwith "Imposible"  in
                   (args, uu____220))
        | uu____242 -> fail ()
  
let rec tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____305 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____305 with
      | (effect_params_un,signature_un,opening) ->
          let uu____312 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un  in
          (match uu____312 with
           | (effect_params,env,uu____318) ->
               let uu____319 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____319 with
                | (signature,uu____323) ->
                    let ed1 =
                      let uu___86_325 = ed  in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___86_325.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___86_325.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___86_325.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___86_325.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___86_325.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___86_325.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___86_325.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___86_325.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___86_325.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___86_325.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___86_325.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___86_325.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___86_325.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___86_325.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___86_325.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___86_325.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___86_325.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___86_325.FStar_Syntax_Syntax.actions)
                      }  in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____329 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts)
                               in
                            ([], t1)  in
                          let uu___87_347 = ed1  in
                          let uu____348 = op ed1.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____349 = op ed1.FStar_Syntax_Syntax.bind_wp
                             in
                          let uu____350 =
                            op ed1.FStar_Syntax_Syntax.if_then_else  in
                          let uu____351 = op ed1.FStar_Syntax_Syntax.ite_wp
                             in
                          let uu____352 = op ed1.FStar_Syntax_Syntax.stronger
                             in
                          let uu____353 = op ed1.FStar_Syntax_Syntax.close_wp
                             in
                          let uu____354 = op ed1.FStar_Syntax_Syntax.assert_p
                             in
                          let uu____355 = op ed1.FStar_Syntax_Syntax.assume_p
                             in
                          let uu____356 = op ed1.FStar_Syntax_Syntax.null_wp
                             in
                          let uu____357 = op ed1.FStar_Syntax_Syntax.trivial
                             in
                          let uu____358 =
                            let uu____359 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr))  in
                            Prims.snd uu____359  in
                          let uu____365 =
                            op ed1.FStar_Syntax_Syntax.return_repr  in
                          let uu____366 =
                            op ed1.FStar_Syntax_Syntax.bind_repr  in
                          let uu____367 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___88_370 = a  in
                                 let uu____371 =
                                   let uu____372 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn))
                                      in
                                   Prims.snd uu____372  in
                                 let uu____378 =
                                   let uu____379 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ))
                                      in
                                   Prims.snd uu____379  in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___88_370.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___88_370.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___88_370.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____371;
                                   FStar_Syntax_Syntax.action_typ = uu____378
                                 }) ed1.FStar_Syntax_Syntax.actions
                             in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___87_347.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___87_347.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___87_347.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___87_347.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___87_347.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___87_347.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____348;
                            FStar_Syntax_Syntax.bind_wp = uu____349;
                            FStar_Syntax_Syntax.if_then_else = uu____350;
                            FStar_Syntax_Syntax.ite_wp = uu____351;
                            FStar_Syntax_Syntax.stronger = uu____352;
                            FStar_Syntax_Syntax.close_wp = uu____353;
                            FStar_Syntax_Syntax.assert_p = uu____354;
                            FStar_Syntax_Syntax.assume_p = uu____355;
                            FStar_Syntax_Syntax.null_wp = uu____356;
                            FStar_Syntax_Syntax.trivial = uu____357;
                            FStar_Syntax_Syntax.repr = uu____358;
                            FStar_Syntax_Syntax.return_repr = uu____365;
                            FStar_Syntax_Syntax.bind_repr = uu____366;
                            FStar_Syntax_Syntax.actions = uu____367
                          }
                       in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____407 =
                          let uu____408 =
                            let uu____411 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t
                               in
                            (uu____411, (FStar_Ident.range_of_lid mname))  in
                          FStar_Errors.Error uu____408  in
                        Prims.raise uu____407  in
                      let uu____416 =
                        let uu____417 =
                          FStar_Syntax_Subst.compress signature1  in
                        uu____417.FStar_Syntax_Syntax.n  in
                      match uu____416 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs  in
                          (match bs1 with
                           | (a,uu____442)::(wp,uu____444)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____453 -> fail signature1)
                      | uu____454 -> fail signature1  in
                    let uu____455 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature
                       in
                    (match uu____455 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____473 =
                           let uu____474 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un
                              in
                           match uu____474 with
                           | (signature1,uu____482) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1
                            in
                         let env1 =
                           let uu____484 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature
                              in
                           FStar_TypeChecker_Env.push_bv env uu____484  in
                         ((let uu____486 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED")
                              in
                           if uu____486
                           then
                             let uu____487 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname
                                in
                             let uu____488 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders
                                in
                             let uu____489 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature
                                in
                             let uu____490 =
                               let uu____491 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               FStar_Syntax_Print.term_to_string uu____491
                                in
                             let uu____492 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort
                                in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____487 uu____488 uu____489 uu____490
                               uu____492
                           else ());
                          (let check_and_gen' env2 uu____505 k =
                             match uu____505 with
                             | (uu____510,t) -> check_and_gen env2 t k  in
                           let return_wp =
                             let expected_k =
                               let uu____516 =
                                 let uu____517 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____518 =
                                   let uu____520 =
                                     let uu____521 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____521
                                      in
                                   [uu____520]  in
                                 uu____517 :: uu____518  in
                               let uu____522 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a  in
                               FStar_Syntax_Util.arrow uu____516 uu____522
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k
                              in
                           let bind_wp =
                             let uu____524 = fresh_effect_signature ()  in
                             match uu____524 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____536 =
                                     let uu____537 =
                                       let uu____538 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____538
                                        in
                                     [uu____537]  in
                                   let uu____539 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____536
                                     uu____539
                                    in
                                 let expected_k =
                                   let uu____541 =
                                     let uu____542 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range
                                        in
                                     let uu____543 =
                                       let uu____545 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____546 =
                                         let uu____548 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____549 =
                                           let uu____551 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let uu____552 =
                                             let uu____554 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b
                                                in
                                             [uu____554]  in
                                           uu____551 :: uu____552  in
                                         uu____548 :: uu____549  in
                                       uu____545 :: uu____546  in
                                     uu____542 :: uu____543  in
                                   let uu____555 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____541
                                     uu____555
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k
                              in
                           let if_then_else1 =
                             let p =
                               let uu____558 =
                                 let uu____559 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____559 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____558
                                in
                             let expected_k =
                               let uu____565 =
                                 let uu____566 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____567 =
                                   let uu____569 =
                                     FStar_Syntax_Syntax.mk_binder p  in
                                   let uu____570 =
                                     let uu____572 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     let uu____573 =
                                       let uu____575 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____575]  in
                                     uu____572 :: uu____573  in
                                   uu____569 :: uu____570  in
                                 uu____566 :: uu____567  in
                               let uu____576 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____565 uu____576
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k
                              in
                           let ite_wp =
                             let expected_k =
                               let uu____579 =
                                 let uu____580 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____581 =
                                   let uu____583 =
                                     FStar_Syntax_Syntax.null_binder wp_a  in
                                   [uu____583]  in
                                 uu____580 :: uu____581  in
                               let uu____584 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____579 uu____584
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k
                              in
                           let stronger =
                             let uu____586 = FStar_Syntax_Util.type_u ()  in
                             match uu____586 with
                             | (t,uu____590) ->
                                 let expected_k =
                                   let uu____592 =
                                     let uu____593 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____594 =
                                       let uu____596 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       let uu____597 =
                                         let uu____599 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [uu____599]  in
                                       uu____596 :: uu____597  in
                                     uu____593 :: uu____594  in
                                   let uu____600 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   FStar_Syntax_Util.arrow uu____592
                                     uu____600
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k
                              in
                           let close_wp =
                             let b =
                               let uu____603 =
                                 let uu____604 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____604 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____603
                                in
                             let b_wp_a =
                               let uu____610 =
                                 let uu____611 =
                                   let uu____612 =
                                     FStar_Syntax_Syntax.bv_to_name b  in
                                   FStar_Syntax_Syntax.null_binder uu____612
                                    in
                                 [uu____611]  in
                               let uu____613 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____610 uu____613
                                in
                             let expected_k =
                               let uu____615 =
                                 let uu____616 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____617 =
                                   let uu____619 =
                                     FStar_Syntax_Syntax.mk_binder b  in
                                   let uu____620 =
                                     let uu____622 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a
                                        in
                                     [uu____622]  in
                                   uu____619 :: uu____620  in
                                 uu____616 :: uu____617  in
                               let uu____623 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____615 uu____623
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k
                              in
                           let assert_p =
                             let expected_k =
                               let uu____626 =
                                 let uu____627 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____628 =
                                   let uu____630 =
                                     let uu____631 =
                                       let uu____632 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____632
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____631
                                      in
                                   let uu____637 =
                                     let uu____639 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____639]  in
                                   uu____630 :: uu____637  in
                                 uu____627 :: uu____628  in
                               let uu____640 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____626 uu____640
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k
                              in
                           let assume_p =
                             let expected_k =
                               let uu____643 =
                                 let uu____644 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____645 =
                                   let uu____647 =
                                     let uu____648 =
                                       let uu____649 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____649
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____648
                                      in
                                   let uu____654 =
                                     let uu____656 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____656]  in
                                   uu____647 :: uu____654  in
                                 uu____644 :: uu____645  in
                               let uu____657 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____643 uu____657
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k
                              in
                           let null_wp =
                             let expected_k =
                               let uu____660 =
                                 let uu____661 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 [uu____661]  in
                               let uu____662 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____660 uu____662
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k
                              in
                           let trivial_wp =
                             let uu____664 = FStar_Syntax_Util.type_u ()  in
                             match uu____664 with
                             | (t,uu____668) ->
                                 let expected_k =
                                   let uu____670 =
                                     let uu____671 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____672 =
                                       let uu____674 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____674]  in
                                     uu____671 :: uu____672  in
                                   let uu____675 =
                                     FStar_Syntax_Syntax.mk_GTotal t  in
                                   FStar_Syntax_Util.arrow uu____670
                                     uu____675
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k
                              in
                           let uu____676 =
                             let uu____682 =
                               let uu____683 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr
                                  in
                               uu____683.FStar_Syntax_Syntax.n  in
                             match uu____682 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____692 ->
                                 let repr =
                                   let uu____694 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____694 with
                                   | (t,uu____698) ->
                                       let expected_k =
                                         let uu____700 =
                                           let uu____701 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____702 =
                                             let uu____704 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____704]  in
                                           uu____701 :: uu____702  in
                                         let uu____705 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow uu____700
                                           uu____705
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
                                   let uu____716 =
                                     let uu____719 =
                                       let uu____720 =
                                         let uu____730 =
                                           let uu____732 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____733 =
                                             let uu____735 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____735]  in
                                           uu____732 :: uu____733  in
                                         (repr1, uu____730)  in
                                       FStar_Syntax_Syntax.Tm_app uu____720
                                        in
                                     FStar_Syntax_Syntax.mk uu____719  in
                                   uu____716 None FStar_Range.dummyRange  in
                                 let mk_repr a1 wp =
                                   let uu____754 =
                                     FStar_Syntax_Syntax.bv_to_name a1  in
                                   mk_repr' uu____754 wp  in
                                 let destruct_repr t =
                                   let uu____765 =
                                     let uu____766 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____766.FStar_Syntax_Syntax.n  in
                                   match uu____765 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____775,(t1,uu____777)::(wp,uu____779)::[])
                                       -> (t1, wp)
                                   | uu____813 ->
                                       failwith "Unexpected repr type"
                                    in
                                 let bind_repr =
                                   let r =
                                     let uu____822 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_All.pipe_right uu____822
                                       FStar_Syntax_Syntax.fv_to_tm
                                      in
                                   let uu____823 = fresh_effect_signature ()
                                      in
                                   match uu____823 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____835 =
                                           let uu____836 =
                                             let uu____837 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____837
                                              in
                                           [uu____836]  in
                                         let uu____838 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____835
                                           uu____838
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
                                         let uu____842 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____842
                                          in
                                       let wp_g_x =
                                         let uu____846 =
                                           let uu____847 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g
                                              in
                                           let uu____848 =
                                             let uu____849 =
                                               let uu____850 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____850
                                                in
                                             [uu____849]  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____847 uu____848
                                            in
                                         uu____846 None
                                           FStar_Range.dummyRange
                                          in
                                       let res =
                                         let wp =
                                           let uu____861 =
                                             let uu____862 =
                                               let uu____863 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp
                                                  in
                                               FStar_All.pipe_right uu____863
                                                 Prims.snd
                                                in
                                             let uu____868 =
                                               let uu____869 =
                                                 let uu____871 =
                                                   let uu____873 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   let uu____874 =
                                                     let uu____876 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b
                                                        in
                                                     let uu____877 =
                                                       let uu____879 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f
                                                          in
                                                       let uu____880 =
                                                         let uu____882 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g
                                                            in
                                                         [uu____882]  in
                                                       uu____879 :: uu____880
                                                        in
                                                     uu____876 :: uu____877
                                                      in
                                                   uu____873 :: uu____874  in
                                                 r :: uu____871  in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____869
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____862 uu____868
                                              in
                                           uu____861 None
                                             FStar_Range.dummyRange
                                            in
                                         mk_repr b wp  in
                                       let expected_k =
                                         let uu____888 =
                                           let uu____889 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____890 =
                                             let uu____892 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b
                                                in
                                             let uu____893 =
                                               let uu____895 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f
                                                  in
                                               let uu____896 =
                                                 let uu____898 =
                                                   let uu____899 =
                                                     let uu____900 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f
                                                        in
                                                     mk_repr a uu____900  in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____899
                                                    in
                                                 let uu____901 =
                                                   let uu____903 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g
                                                      in
                                                   let uu____904 =
                                                     let uu____906 =
                                                       let uu____907 =
                                                         let uu____908 =
                                                           let uu____909 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a
                                                              in
                                                           [uu____909]  in
                                                         let uu____910 =
                                                           let uu____911 =
                                                             mk_repr b wp_g_x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____911
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           uu____908
                                                           uu____910
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____907
                                                        in
                                                     [uu____906]  in
                                                   uu____903 :: uu____904  in
                                                 uu____898 :: uu____901  in
                                               uu____895 :: uu____896  in
                                             uu____892 :: uu____893  in
                                           uu____889 :: uu____890  in
                                         let uu____912 =
                                           FStar_Syntax_Syntax.mk_Total res
                                            in
                                         FStar_Syntax_Util.arrow uu____888
                                           uu____912
                                          in
                                       let uu____913 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k
                                          in
                                       (match uu____913 with
                                        | (expected_k1,uu____918,uu____919)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let env3 =
                                              let uu___89_923 = env2  in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___89_923.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___89_923.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___89_923.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___89_923.FStar_TypeChecker_Env.qname_and_index)
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
                                     let uu____930 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____930
                                      in
                                   let res =
                                     let wp =
                                       let uu____937 =
                                         let uu____938 =
                                           let uu____939 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp
                                              in
                                           FStar_All.pipe_right uu____939
                                             Prims.snd
                                            in
                                         let uu____944 =
                                           let uu____945 =
                                             let uu____947 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             let uu____948 =
                                               let uu____950 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               [uu____950]  in
                                             uu____947 :: uu____948  in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____945
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____938 uu____944
                                          in
                                       uu____937 None FStar_Range.dummyRange
                                        in
                                     mk_repr a wp  in
                                   let expected_k =
                                     let uu____956 =
                                       let uu____957 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____958 =
                                         let uu____960 =
                                           FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                         [uu____960]  in
                                       uu____957 :: uu____958  in
                                     let uu____961 =
                                       FStar_Syntax_Syntax.mk_Total res  in
                                     FStar_Syntax_Util.arrow uu____956
                                       uu____961
                                      in
                                   let uu____962 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k
                                      in
                                   match uu____962 with
                                   | (expected_k1,uu____970,uu____971) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (Prims.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                          in
                                       let uu____974 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1
                                          in
                                       (match uu____974 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____986 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos)))))
                                    in
                                 let actions =
                                   let check_action act =
                                     let uu____997 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ
                                        in
                                     match uu____997 with
                                     | (act_typ,uu____1002,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env1 act_typ
                                            in
                                         ((let uu____1006 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED")
                                              in
                                           if uu____1006
                                           then
                                             let uu____1007 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn
                                                in
                                             let uu____1008 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ
                                                in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1007 uu____1008
                                           else ());
                                          (let uu____1010 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn
                                              in
                                           match uu____1010 with
                                           | (act_defn,uu____1015,g_a) ->
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
                                               let uu____1019 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1
                                                    in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1037 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____1037 with
                                                      | (bs1,uu____1043) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let k =
                                                            let uu____1048 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1048
                                                             in
                                                          let uu____1049 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k
                                                             in
                                                          (match uu____1049
                                                           with
                                                           | (k1,uu____1056,g)
                                                               -> (k1, g)))
                                                 | uu____1058 ->
                                                     let uu____1059 =
                                                       let uu____1060 =
                                                         let uu____1063 =
                                                           let uu____1064 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2
                                                              in
                                                           let uu____1065 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2
                                                              in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1064
                                                             uu____1065
                                                            in
                                                         (uu____1063,
                                                           (act_defn1.FStar_Syntax_Syntax.pos))
                                                          in
                                                       FStar_Errors.Error
                                                         uu____1060
                                                        in
                                                     Prims.raise uu____1059
                                                  in
                                               (match uu____1019 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k
                                                       in
                                                    ((let uu____1072 =
                                                        let uu____1073 =
                                                          let uu____1074 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g
                                                             in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1074
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1073
                                                         in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1072);
                                                     (let act_typ2 =
                                                        let uu____1076 =
                                                          let uu____1077 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k
                                                             in
                                                          uu____1077.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____1076 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1092 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____1092
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1097
                                                                   =
                                                                   let uu____1104
                                                                    =
                                                                    FStar_TypeChecker_Env.result_typ
                                                                    env1 c1
                                                                     in
                                                                   destruct_repr
                                                                    uu____1104
                                                                    in
                                                                 (match uu____1097
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1116
                                                                    =
                                                                    let uu____1117
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1117]
                                                                     in
                                                                    let uu____1118
                                                                    =
                                                                    let uu____1124
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    a1  in
                                                                    let uu____1125
                                                                    =
                                                                    let uu____1127
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1127]
                                                                     in
                                                                    uu____1124
                                                                    ::
                                                                    uu____1125
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1116;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1118;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1128
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1128))
                                                        | uu____1129 ->
                                                            failwith ""
                                                         in
                                                      let uu____1130 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1
                                                         in
                                                      match uu____1130 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2
                                                             in
                                                          let uu___90_1136 =
                                                            act  in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___90_1136.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___90_1136.FStar_Syntax_Syntax.action_unqualified_name);
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
                           match uu____676 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 FStar_Syntax_Util.maybe_tot_arrow
                                   ed2.FStar_Syntax_Syntax.binders
                                   ed2.FStar_Syntax_Syntax.signature
                                  in
                               let uu____1150 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t
                                  in
                               (match uu____1150 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1156 =
                                        let uu____1159 =
                                          let uu____1160 =
                                            FStar_Syntax_Subst.compress t1
                                             in
                                          uu____1160.FStar_Syntax_Syntax.n
                                           in
                                        (effect_params, uu____1159)  in
                                      match uu____1156 with
                                      | ([],uu____1163) -> t1
                                      | (uu____1169,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1170,c)) ->
                                          FStar_TypeChecker_Env.result_typ
                                            env0 c
                                      | uu____1182 -> failwith "Impossible"
                                       in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1193 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts
                                           in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1193
                                         in
                                      let m =
                                        FStar_List.length (Prims.fst ts1)  in
                                      (let uu____1198 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1199 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1)
                                                in
                                             Prims.op_Negation uu____1199))
                                           && (m <> n1)
                                          in
                                       if uu____1198
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic"
                                            in
                                         let uu____1208 =
                                           let uu____1209 =
                                             FStar_Util.string_of_int n1  in
                                           let uu____1210 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1
                                              in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1209 uu____1210
                                            in
                                         failwith uu____1208
                                       else ());
                                      ts1  in
                                    let close_action act =
                                      let uu____1216 =
                                        close1 (~- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn))
                                         in
                                      match uu____1216 with
                                      | (univs2,defn) ->
                                          let uu____1221 =
                                            close1 (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ))
                                             in
                                          (match uu____1221 with
                                           | (univs',typ) ->
                                               let uu___91_1227 = act  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___91_1227.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___91_1227.FStar_Syntax_Syntax.action_unqualified_name);
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
                                      let uu___92_1232 = ed2  in
                                      let uu____1233 =
                                        close1 (Prims.parse_int "0")
                                          return_wp
                                         in
                                      let uu____1234 =
                                        close1 (Prims.parse_int "1") bind_wp
                                         in
                                      let uu____1235 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1
                                         in
                                      let uu____1236 =
                                        close1 (Prims.parse_int "0") ite_wp
                                         in
                                      let uu____1237 =
                                        close1 (Prims.parse_int "0") stronger
                                         in
                                      let uu____1238 =
                                        close1 (Prims.parse_int "1") close_wp
                                         in
                                      let uu____1239 =
                                        close1 (Prims.parse_int "0") assert_p
                                         in
                                      let uu____1240 =
                                        close1 (Prims.parse_int "0") assume_p
                                         in
                                      let uu____1241 =
                                        close1 (Prims.parse_int "0") null_wp
                                         in
                                      let uu____1242 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp
                                         in
                                      let uu____1243 =
                                        let uu____1244 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr)
                                           in
                                        Prims.snd uu____1244  in
                                      let uu____1250 =
                                        close1 (Prims.parse_int "0")
                                          return_repr
                                         in
                                      let uu____1251 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr
                                         in
                                      let uu____1252 =
                                        FStar_List.map close_action actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___92_1232.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___92_1232.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___92_1232.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1233;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1234;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1235;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1236;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1237;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1238;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1239;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1240;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1241;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1242;
                                        FStar_Syntax_Syntax.repr = uu____1243;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1250;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1251;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1252
                                      }  in
                                    ((let uu____1255 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED"))
                                         in
                                      if uu____1255
                                      then
                                        let uu____1256 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print_string uu____1256
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
      let uu____1260 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1260 with
      | (effect_binders_un,signature_un) ->
          let uu____1270 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1270 with
           | (effect_binders,env1,uu____1281) ->
               let uu____1282 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1282 with
                | (signature,uu____1291) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1300  ->
                           match uu____1300 with
                           | (bv,qual) ->
                               let uu____1307 =
                                 let uu___93_1308 = bv  in
                                 let uu____1309 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___93_1308.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___93_1308.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1309
                                 }  in
                               (uu____1307, qual)) effect_binders
                       in
                    let uu____1312 =
                      let uu____1317 =
                        let uu____1318 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____1318.FStar_Syntax_Syntax.n  in
                      match uu____1317 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1326)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1341 ->
                          failwith "bad shape for effect-for-free signature"
                       in
                    (match uu____1312 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1358 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____1358
                           then
                             let uu____1359 =
                               let uu____1361 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               Some uu____1361  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1359
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders1
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____1371 =
                             FStar_TypeChecker_TcTerm.tc_term env1 t1  in
                           match uu____1371 with
                           | (t2,comp,uu____1379) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____1390 =
                           open_and_check ed.FStar_Syntax_Syntax.repr  in
                         (match uu____1390 with
                          | (repr,_comp) ->
                              ((let uu____1401 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____1401
                                then
                                  let uu____1402 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1402
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
                                  let uu____1408 =
                                    let uu____1409 =
                                      let uu____1410 =
                                        let uu____1420 =
                                          let uu____1424 =
                                            let uu____1427 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____1428 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____1427, uu____1428)  in
                                          [uu____1424]  in
                                        (wp_type1, uu____1420)  in
                                      FStar_Syntax_Syntax.Tm_app uu____1410
                                       in
                                    mk1 uu____1409  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1408
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____1443 =
                                      let uu____1446 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____1446)  in
                                    let uu____1447 =
                                      let uu____1451 =
                                        let uu____1452 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a
                                           in
                                        FStar_All.pipe_right uu____1452
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____1451]  in
                                    uu____1443 :: uu____1447  in
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
                                  let uu____1485 = item  in
                                  match uu____1485 with
                                  | (u_item,item1) ->
                                      let uu____1497 = open_and_check item1
                                         in
                                      (match uu____1497 with
                                       | (item2,item_comp) ->
                                           ((let uu____1507 =
                                               let uu____1508 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____1508
                                                in
                                             if uu____1507
                                             then
                                               let uu____1509 =
                                                 let uu____1510 =
                                                   let uu____1511 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____1512 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1511 uu____1512
                                                    in
                                                 FStar_Errors.Err uu____1510
                                                  in
                                               Prims.raise uu____1509
                                             else ());
                                            (let uu____1514 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____1514 with
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
                                let uu____1527 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____1527 with
                                | (dmff_env1,uu____1538,bind_wp,bind_elab) ->
                                    let uu____1541 =
                                      elaborate_and_star dmff_env1
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____1541 with
                                     | (dmff_env2,uu____1552,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1556 =
                                             let uu____1557 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1557.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1556 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1595 =
                                                 let uu____1603 =
                                                   let uu____1606 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1606
                                                    in
                                                 match uu____1603 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1645 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____1595 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1667 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1667 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let uu____1675 =
                                                        let uu____1676 =
                                                          let uu____1677 =
                                                            let uu____1687 =
                                                              let uu____1691
                                                                =
                                                                let uu____1694
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11)
                                                                   in
                                                                let uu____1695
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____1694,
                                                                  uu____1695)
                                                                 in
                                                              [uu____1691]
                                                               in
                                                            (wp_type1,
                                                              uu____1687)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1677
                                                           in
                                                        mk1 uu____1676  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 uu____1675
                                                       in
                                                    let uu____1703 =
                                                      let uu____1713 =
                                                        let uu____1714 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____1714
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1713
                                                       in
                                                    (match uu____1703 with
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
                                                           let uu____1747 =
                                                             let uu____1748 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp
                                                                in
                                                             let uu____1749 =
                                                               let uu____1750
                                                                 =
                                                                 let uu____1754
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'
                                                                    in
                                                                 (uu____1754,
                                                                   None)
                                                                  in
                                                               [uu____1750]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____1748
                                                               uu____1749
                                                              in
                                                           uu____1747 None
                                                             FStar_Range.dummyRange
                                                            in
                                                         let uu____1770 =
                                                           let uu____1774 =
                                                             let uu____1778 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp
                                                                in
                                                             [uu____1778]  in
                                                           b11 :: uu____1774
                                                            in
                                                         let uu____1781 =
                                                           FStar_Syntax_Util.abs
                                                             bs1 body3 what
                                                            in
                                                         FStar_Syntax_Util.abs
                                                           uu____1770
                                                           uu____1781
                                                           (Some
                                                              (FStar_Util.Inr
                                                                 (FStar_Syntax_Const.effect_GTot_lid,
                                                                   [])))))
                                           | uu____1791 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let return_wp1 =
                                           let uu____1793 =
                                             let uu____1794 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1794.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1793 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1832 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1832
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1848 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let bind_wp1 =
                                           let uu____1850 =
                                             let uu____1851 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____1851.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1850 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None
                                                  in
                                               let uu____1880 =
                                                 let uu____1884 =
                                                   let uu____1886 =
                                                     let uu____1887 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____1887
                                                      in
                                                   [uu____1886]  in
                                                 FStar_List.append uu____1884
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____1880 body what
                                           | uu____1888 ->
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
                                             (let uu____1906 =
                                                let uu____1907 =
                                                  let uu____1908 =
                                                    let uu____1918 =
                                                      let uu____1919 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      Prims.snd uu____1919
                                                       in
                                                    (t, uu____1918)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____1908
                                                   in
                                                mk1 uu____1907  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____1906)
                                            in
                                         let register name item =
                                           let uu____1931 =
                                             let uu____1934 = mk_lid name  in
                                             let uu____1935 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item None
                                                in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____1934 uu____1935
                                              in
                                           match uu____1931 with
                                           | (sigelt,fv) ->
                                               ((let uu____1944 =
                                                   let uu____1946 =
                                                     FStar_ST.read sigelts
                                                      in
                                                   sigelt :: uu____1946  in
                                                 FStar_ST.write sigelts
                                                   uu____1944);
                                                fv)
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____1957 =
                                             let uu____1959 =
                                               FStar_ST.read sigelts  in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____1959
                                              in
                                           FStar_ST.write sigelts uu____1957);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____1969 =
                                              let uu____1971 =
                                                FStar_ST.read sigelts  in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: uu____1971
                                               in
                                            FStar_ST.write sigelts uu____1969);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____1981 =
                                               let uu____1983 =
                                                 FStar_ST.read sigelts  in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: uu____1983
                                                in
                                             FStar_ST.write sigelts
                                               uu____1981);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____1993 =
                                                let uu____1995 =
                                                  FStar_ST.read sigelts  in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: uu____1995
                                                 in
                                              FStar_ST.write sigelts
                                                uu____1993);
                                             (let uu____2003 =
                                                FStar_List.fold_left
                                                  (fun uu____2010  ->
                                                     fun action  ->
                                                       match uu____2010 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let uu____2022 =
                                                             elaborate_and_star
                                                               dmff_env3
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn))
                                                              in
                                                           (match uu____2022
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
                                                                let uu____2038
                                                                  =
                                                                  let uu____2040
                                                                    =
                                                                    let uu___94_2041
                                                                    = action
                                                                     in
                                                                    let uu____2042
                                                                    =
                                                                    apply_close
                                                                    action_elab1
                                                                     in
                                                                    let uu____2043
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___94_2041.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___94_2041.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___94_2041.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2042;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2043
                                                                    }  in
                                                                  uu____2040
                                                                    ::
                                                                    actions
                                                                   in
                                                                (dmff_env4,
                                                                  uu____2038)))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____2003 with
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
                                                      let uu____2061 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____2062 =
                                                        let uu____2064 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____2064]  in
                                                      uu____2061 ::
                                                        uu____2062
                                                       in
                                                    let uu____2065 =
                                                      let uu____2066 =
                                                        let uu____2067 =
                                                          let uu____2068 =
                                                            let uu____2078 =
                                                              let uu____2082
                                                                =
                                                                let uu____2085
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____2086
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2085,
                                                                  uu____2086)
                                                                 in
                                                              [uu____2082]
                                                               in
                                                            (repr,
                                                              uu____2078)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2068
                                                           in
                                                        mk1 uu____2067  in
                                                      let uu____2094 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2066
                                                        uu____2094
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2065 None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____2102 =
                                                    let uu____2105 =
                                                      let uu____2106 =
                                                        let uu____2109 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2109
                                                         in
                                                      uu____2106.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2105 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2115)
                                                        ->
                                                        let uu____2142 =
                                                          let uu____2151 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____2151
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2182 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____2142
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2208 =
                                                               let uu____2209
                                                                 =
                                                                 let uu____2212
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2212
                                                                  in
                                                               uu____2209.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____2208
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2227
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____2227
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2234
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2245
                                                                     ->
                                                                    match uu____2245
                                                                    with
                                                                    | 
                                                                    (bv,uu____2249)
                                                                    ->
                                                                    let uu____2250
                                                                    =
                                                                    let uu____2251
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2251
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2250
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2234
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
                                                                    uu____2282
                                                                    ->
                                                                    let uu____2286
                                                                    =
                                                                    let uu____2287
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2287
                                                                     in
                                                                    failwith
                                                                    uu____2286
                                                                     in
                                                                    let uu____2290
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2291
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None  in
                                                                    (uu____2290,
                                                                    uu____2291)))
                                                              | uu____2299 ->
                                                                  let uu____2300
                                                                    =
                                                                    let uu____2301
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2301
                                                                     in
                                                                  failwith
                                                                    uu____2300))
                                                    | uu____2304 ->
                                                        let uu____2305 =
                                                          let uu____2306 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1
                                                             in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2306
                                                           in
                                                        failwith uu____2305
                                                     in
                                                  (match uu____2102 with
                                                   | (pre,post) ->
                                                       ((let uu____2317 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____2319 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____2321 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___95_2323 =
                                                             ed  in
                                                           let uu____2324 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____2325 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____2326 =
                                                             let uu____2327 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____2327)
                                                              in
                                                           let uu____2333 =
                                                             let uu____2334 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____2334)
                                                              in
                                                           let uu____2340 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____2341 =
                                                             let uu____2342 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____2342)
                                                              in
                                                           let uu____2348 =
                                                             let uu____2349 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____2349)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2324;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2325;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2326;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2333;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___95_2323.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2340;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2341;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2348;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____2355 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____2355
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2366
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____2366
                                                               then
                                                                 let uu____2367
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____2367
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
                                                                    let uu____2385
                                                                    =
                                                                    let uu____2387
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    Some
                                                                    uu____2387
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
                                                                    uu____2385;
                                                                    FStar_Syntax_Syntax.sub_eff_lift
                                                                    = None
                                                                    }  in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None
                                                                  in
                                                               let uu____2395
                                                                 =
                                                                 let uu____2397
                                                                   =
                                                                   let uu____2399
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____2399
                                                                    in
                                                                 FStar_List.append
                                                                   uu____2397
                                                                   sigelts'
                                                                  in
                                                               (uu____2395,
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
              (lex_t1,[],[],t,uu____2422,uu____2423,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top1,[],_t_top,_lex_t_top,_0_28,[],uu____2428,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2433,r2))::[]
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
                let uu____2477 =
                  let uu____2480 =
                    let uu____2481 =
                      let uu____2486 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None
                         in
                      (uu____2486, [FStar_Syntax_Syntax.U_name utop])  in
                    FStar_Syntax_Syntax.Tm_uinst uu____2481  in
                  FStar_Syntax_Syntax.mk uu____2480  in
                uu____2477 None r1  in
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
                  let uu____2505 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2505  in
                let hd1 =
                  let uu____2511 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2511  in
                let tl1 =
                  let uu____2513 =
                    let uu____2514 =
                      let uu____2517 =
                        let uu____2518 =
                          let uu____2523 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None
                             in
                          (uu____2523, [FStar_Syntax_Syntax.U_name ucons2])
                           in
                        FStar_Syntax_Syntax.Tm_uinst uu____2518  in
                      FStar_Syntax_Syntax.mk uu____2517  in
                    uu____2514 None r2  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2513  in
                let res =
                  let uu____2536 =
                    let uu____2539 =
                      let uu____2540 =
                        let uu____2545 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None
                           in
                        (uu____2545,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]])
                         in
                      FStar_Syntax_Syntax.Tm_uinst uu____2540  in
                    FStar_Syntax_Syntax.mk uu____2539  in
                  uu____2536 None r2  in
                let uu____2555 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2555
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
              let uu____2576 =
                let uu____2584 = FStar_TypeChecker_Env.get_range env  in
                ([tc; dc_lextop; dc_lexcons], [], lids, uu____2584)  in
              FStar_Syntax_Syntax.Sig_bundle uu____2576
          | uu____2588 ->
              let uu____2590 =
                let uu____2591 =
                  FStar_Syntax_Print.sigelt_to_string
                    (FStar_Syntax_Syntax.Sig_bundle
                       (ses, [], lids, FStar_Range.dummyRange))
                   in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2591  in
              failwith uu____2590

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
            let uu____2602 = FStar_Syntax_Util.type_u ()  in
            match uu____2602 with
            | (k,uu____2606) ->
                let phi1 =
                  let uu____2608 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____2608
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
          let uu____2619 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids
             in
          match uu____2619 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2638 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas
                   in
                FStar_All.pipe_right uu____2638 FStar_List.flatten  in
              ((let uu____2646 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____2646
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
                          let uu____2652 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2658,uu____2659,uu____2660,uu____2661,uu____2662,uu____2663,r)
                                -> (lid, r)
                            | uu____2671 -> failwith "Impossible!"  in
                          match uu____2652 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2680 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2684,uu____2685,uu____2686,uu____2687,uu____2688,uu____2689,uu____2690)
                        -> lid
                    | uu____2697 -> failwith "Impossible"  in
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
                let uu____2703 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____2703
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
                   let uu____2719 =
                     let uu____2721 =
                       let uu____2722 =
                         let uu____2730 =
                           FStar_TypeChecker_Env.get_range env0  in
                         ((FStar_List.append tcs datas), quals, lids,
                           uu____2730)
                          in
                       FStar_Syntax_Syntax.Sig_bundle uu____2722  in
                     uu____2721 :: ses1  in
                   (uu____2719, data_ops_ses))))

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
           let uu____2770 = FStar_TypeChecker_Env.push_sigelt env2 se1  in
           ([se1], uu____2770, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____2784 = tc_inductive env2 ses quals lids  in
           (match uu____2784 with
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
             let uu____2814 = FStar_Options.set_options t s  in
             match uu____2814 with
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
                ((let uu____2832 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____2832 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env1, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____2840 = cps_and_elaborate env1 ne  in
           (match uu____2840 with
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
           let uu____2869 =
             FStar_All.pipe_right ne1.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____2880  ->
                     fun a  ->
                       match uu____2880 with
                       | (env3,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne1.FStar_Syntax_Syntax.mname a
                              in
                           let uu____2893 =
                             FStar_TypeChecker_Env.push_sigelt env3 se_let
                              in
                           (uu____2893, (se_let :: ses))) (env2, [se1]))
              in
           (match uu____2869 with
            | (env3,ses) ->
                let env4 = FStar_TypeChecker_Util.build_lattice env3 se1  in
                ([se1], env4, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub1,r) ->
           let env0 = env1  in
           let uu____2911 = FStar_Syntax_Subst.open_sub_eff sub1  in
           (match uu____2911 with
            | (uvs,bs,sub2) ->
                let env2 = FStar_TypeChecker_Env.push_univ_vars env1 uvs  in
                let uu____2924 = FStar_TypeChecker_TcTerm.tc_tparams env0 bs
                   in
                (match uu____2924 with
                 | (effect_binders,env3,uu____2935) ->
                     ((let uu____2937 =
                         FStar_Syntax_Print.sigelt_to_string
                           (FStar_Syntax_Syntax.Sig_sub_effect (sub2, r))
                          in
                       FStar_Util.print1 "After opening a sub effect %s\n"
                         uu____2937);
                      (let source =
                         (sub2.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
                          in
                       let target =
                         (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
                          in
                       let ed_src =
                         FStar_TypeChecker_Env.get_effect_decl env3 source
                          in
                       let ed_tgt =
                         FStar_TypeChecker_Env.get_effect_decl env3 target
                          in
                       let effect_wp_typ effect_lid effect_args =
                         let uu____2949 =
                           let uu____2957 =
                             FStar_TypeChecker_Env.lookup_effect_lid env3
                               effect_lid
                              in
                           monad_signature env3 effect_lid uu____2957  in
                         match uu____2949 with
                         | (effect_bs,wp_typ) ->
                             let effect_args_sub =
                               FStar_List.map2
                                 (fun uu____2978  ->
                                    fun uu____2979  ->
                                      match (uu____2978, uu____2979) with
                                      | ((x,uu____2993),(arg,uu____2995)) ->
                                          FStar_Syntax_Syntax.NT (x, arg))
                                 effect_bs effect_args
                                in
                             FStar_Syntax_Subst.subst effect_args_sub wp_typ
                          in
                       let src_wp =
                         effect_wp_typ source
                           (sub2.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                          in
                       let tgt_wp =
                         effect_wp_typ target
                           (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.effect_args
                          in
                       let uu____3010 =
                         match ((sub2.FStar_Syntax_Syntax.sub_eff_lift),
                                 (sub2.FStar_Syntax_Syntax.sub_eff_lift_wp))
                         with
                         | (None ,None ) ->
                             failwith
                               "Impossible : a subEffect without any lift should not be generated by desugaring"
                         | (lift,Some lift_wp) ->
                             let expected_k =
                               let uu____3030 =
                                 let uu____3031 =
                                   FStar_Syntax_Syntax.null_binder src_wp  in
                                 [uu____3031]  in
                               let uu____3032 =
                                 FStar_Syntax_Syntax.mk_Total tgt_wp  in
                               FStar_Syntax_Util.arrow uu____3030 uu____3032
                                in
                             let uu____3033 =
                               tc_check_trivial_guard env3 lift_wp expected_k
                                in
                             (lift, uu____3033)
                         | (Some lift,None ) ->
                             let dmff_env =
                               FStar_TypeChecker_DMFF.empty env3
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange)
                                in
                             let uu____3039 =
                               FStar_TypeChecker_DMFF.star_expr dmff_env lift
                                in
                             (match uu____3039 with
                              | (uu____3046,lift_wp,lift_elab) ->
                                  let uu____3049 =
                                    recheck_debug "lift-wp" env3 lift_wp  in
                                  let uu____3050 =
                                    recheck_debug "lift-elab" env3 lift_elab
                                     in
                                  ((Some lift_elab), lift_wp))
                          in
                       match uu____3010 with
                       | (lift,lift_wp) ->
                           let env4 =
                             let uu___96_3062 = env3  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___96_3062.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___96_3062.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___96_3062.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___96_3062.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___96_3062.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___96_3062.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___96_3062.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___96_3062.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___96_3062.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___96_3062.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___96_3062.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___96_3062.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___96_3062.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___96_3062.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___96_3062.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___96_3062.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___96_3062.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___96_3062.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___96_3062.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___96_3062.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___96_3062.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___96_3062.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___96_3062.FStar_TypeChecker_Env.qname_and_index)
                             }  in
                           let repr_type eff_name effect_args wp =
                             let no_reify l =
                               let uu____3083 =
                                 let uu____3084 =
                                   let uu____3087 =
                                     FStar_Util.format1
                                       "Effect %s cannot be reified"
                                       l.FStar_Ident.str
                                      in
                                   let uu____3088 =
                                     FStar_TypeChecker_Env.get_range env4  in
                                   (uu____3087, uu____3088)  in
                                 FStar_Errors.Error uu____3084  in
                               Prims.raise uu____3083  in
                             let uu____3091 =
                               FStar_TypeChecker_Env.effect_decl_opt env4
                                 eff_name
                                in
                             match uu____3091 with
                             | None  -> no_reify eff_name
                             | Some ed ->
                                 let univ_inst =
                                   FStar_List.map
                                     (fun uu____3098  ->
                                        FStar_Syntax_Syntax.U_unknown)
                                     ed.FStar_Syntax_Syntax.univs
                                    in
                                 let repr =
                                   FStar_TypeChecker_Env.inst_effect_fun_with
                                     univ_inst env4 ed
                                     ([], (ed.FStar_Syntax_Syntax.repr))
                                    in
                                 let uu____3101 =
                                   let uu____3102 =
                                     FStar_All.pipe_right
                                       ed.FStar_Syntax_Syntax.qualifiers
                                       (FStar_List.contains
                                          FStar_Syntax_Syntax.Reifiable)
                                      in
                                   Prims.op_Negation uu____3102  in
                                 if uu____3101
                                 then no_reify eff_name
                                 else
                                   (let uu____3107 =
                                      FStar_TypeChecker_Env.get_range env4
                                       in
                                    let uu____3108 =
                                      let uu____3111 =
                                        let uu____3112 =
                                          let uu____3122 =
                                            let uu____3124 =
                                              let uu____3126 =
                                                FStar_Syntax_Syntax.as_arg wp
                                                 in
                                              [uu____3126]  in
                                            FStar_List.append effect_args
                                              uu____3124
                                             in
                                          (repr, uu____3122)  in
                                        FStar_Syntax_Syntax.Tm_app uu____3112
                                         in
                                      FStar_Syntax_Syntax.mk uu____3111  in
                                    uu____3108 None uu____3107)
                              in
                           let tc_lift lift1 =
                             let wp_a =
                               FStar_Syntax_Syntax.new_bv None src_wp  in
                             let wp_a_typ =
                               FStar_Syntax_Syntax.bv_to_name wp_a  in
                             let binders_to_names =
                               FStar_List.map
                                 (fun uu____3151  ->
                                    match uu____3151 with
                                    | (bv,uu____3155) ->
                                        FStar_Syntax_Syntax.bv_to_name bv)
                                in
                             let repr_f =
                               repr_type source
                                 (sub2.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                                 wp_a_typ
                                in
                             let repr_result =
                               let lift_wp1 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.EraseUniverses;
                                   FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                   env4 lift_wp
                                  in
                               let lift_wp_a =
                                 let uu____3166 =
                                   FStar_TypeChecker_Env.get_range env4  in
                                 let uu____3167 =
                                   let uu____3170 =
                                     let uu____3171 =
                                       let uu____3181 =
                                         let uu____3183 =
                                           FStar_Syntax_Syntax.as_arg
                                             wp_a_typ
                                            in
                                         [uu____3183]  in
                                       (lift_wp1, uu____3181)  in
                                     FStar_Syntax_Syntax.Tm_app uu____3171
                                      in
                                   FStar_Syntax_Syntax.mk uu____3170  in
                                 uu____3167 None uu____3166  in
                               repr_type target
                                 (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.effect_args
                                 lift_wp_a
                                in
                             let expected_k =
                               let bs1 =
                                 let uu____3196 =
                                   FStar_Syntax_Syntax.mk_binder wp_a  in
                                 let uu____3197 =
                                   let uu____3199 =
                                     FStar_Syntax_Syntax.null_binder repr_f
                                      in
                                   [uu____3199]  in
                                 uu____3196 :: uu____3197  in
                               let uu____3200 =
                                 FStar_Syntax_Syntax.mk_Total repr_result  in
                               FStar_Syntax_Util.arrow bs1 uu____3200  in
                             let uu____3201 =
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 env4 expected_k
                                in
                             match uu____3201 with
                             | (expected_k1,uu____3206,uu____3207) ->
                                 tc_check_trivial_guard env4 lift1
                                   expected_k1
                              in
                           let lift1 = FStar_Util.map_opt lift tc_lift  in
                           let env5 = env0  in
                           let univs1 =
                             let t =
                               let wp_a =
                                 FStar_Syntax_Syntax.new_bv None src_wp  in
                               let wp_a_typ =
                                 FStar_Syntax_Syntax.bv_to_name wp_a  in
                               let complete_effect ct wp =
                                 let uu____3225 =
                                   let uu____3228 =
                                     let uu____3229 =
                                       let uu___97_3230 = ct  in
                                       let uu____3231 =
                                         let uu____3237 =
                                           let uu____3243 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____3243]  in
                                         FStar_List.append
                                           ct.FStar_Syntax_Syntax.effect_args
                                           uu____3237
                                          in
                                       {
                                         FStar_Syntax_Syntax.comp_typ_name =
                                           (uu___97_3230.FStar_Syntax_Syntax.comp_typ_name);
                                         FStar_Syntax_Syntax.comp_univs =
                                           (uu___97_3230.FStar_Syntax_Syntax.comp_univs);
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____3231;
                                         FStar_Syntax_Syntax.flags =
                                           (uu___97_3230.FStar_Syntax_Syntax.flags)
                                       }  in
                                     FStar_Syntax_Syntax.Comp uu____3229  in
                                   FStar_Syntax_Syntax.mk uu____3228  in
                                 uu____3225 None FStar_Range.dummyRange  in
                               let src_eff =
                                 let uu____3257 =
                                   let uu____3258 =
                                     FStar_Syntax_Syntax.null_binder
                                       FStar_TypeChecker_Common.t_unit
                                      in
                                   [uu____3258]  in
                                 let uu____3259 =
                                   complete_effect
                                     sub2.FStar_Syntax_Syntax.sub_eff_source
                                     wp_a_typ
                                    in
                                 FStar_Syntax_Util.arrow uu____3257
                                   uu____3259
                                  in
                               let tgt_eff =
                                 let lifted_wp =
                                   let uu____3266 =
                                     let uu____3267 =
                                       let uu____3268 =
                                         FStar_Syntax_Syntax.as_arg wp_a_typ
                                          in
                                       [uu____3268]  in
                                     FStar_Syntax_Syntax.mk_Tm_app lift_wp
                                       uu____3267
                                      in
                                   uu____3266 None FStar_Range.dummyRange  in
                                 complete_effect
                                   sub2.FStar_Syntax_Syntax.sub_eff_target
                                   lifted_wp
                                  in
                               let uu____3273 =
                                 let uu____3274 =
                                   let uu____3278 =
                                     FStar_Syntax_Syntax.mk_binder wp_a  in
                                   let uu____3279 =
                                     let uu____3281 =
                                       FStar_Syntax_Syntax.null_binder
                                         src_eff
                                        in
                                     [uu____3281]  in
                                   uu____3278 :: uu____3279  in
                                 FStar_List.append effect_binders uu____3274
                                  in
                               FStar_Syntax_Util.arrow uu____3273 tgt_eff  in
                             let uu____3284 =
                               FStar_TypeChecker_Util.generalize_universes
                                 env0 t
                                in
                             FStar_All.pipe_right uu____3284 Prims.fst  in
                           let sub3 =
                             let uu___98_3288 = sub2  in
                             {
                               FStar_Syntax_Syntax.sub_eff_univs = univs1;
                               FStar_Syntax_Syntax.sub_eff_binders =
                                 effect_binders;
                               FStar_Syntax_Syntax.sub_eff_source =
                                 (uu___98_3288.FStar_Syntax_Syntax.sub_eff_source);
                               FStar_Syntax_Syntax.sub_eff_target =
                                 (uu___98_3288.FStar_Syntax_Syntax.sub_eff_target);
                               FStar_Syntax_Syntax.sub_eff_lift_wp =
                                 (Some lift_wp);
                               FStar_Syntax_Syntax.sub_eff_lift = lift1
                             }  in
                           let sub4 = FStar_Syntax_Subst.close_sub_eff sub3
                              in
                           let se1 =
                             FStar_Syntax_Syntax.Sig_sub_effect (sub4, r)  in
                           let env6 =
                             FStar_TypeChecker_Env.push_sigelt env5 se1  in
                           let env7 =
                             FStar_TypeChecker_Util.build_lattice env6 se1
                              in
                           ([se1], env7, [])))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3309 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____3309 with
            | (tps1,c1) ->
                let uu____3319 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____3319 with
                 | (tps2,env3,us) ->
                     let uu____3331 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____3331 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____3346 =
                              let uu____3347 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3347
                               in
                            match uu____3346 with
                            | (uvs1,t) ->
                                let uu____3361 =
                                  let uu____3369 =
                                    let uu____3372 =
                                      let uu____3373 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____3373.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____3372)  in
                                  match uu____3369 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3383,c4)) -> ([], c4)
                                  | (uu____3407,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3425 -> failwith "Impossible"  in
                                (match uu____3361 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3455 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____3455 with
                                         | (uu____3458,t1) ->
                                             let uu____3460 =
                                               let uu____3461 =
                                                 let uu____3464 =
                                                   let uu____3465 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid
                                                      in
                                                   let uu____3466 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int
                                                      in
                                                   let uu____3469 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3465 uu____3466
                                                     uu____3469
                                                    in
                                                 (uu____3464, r)  in
                                               FStar_Errors.Error uu____3461
                                                in
                                             Prims.raise uu____3460)
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
                (fun uu___78_3499  ->
                   match uu___78_3499 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3500 -> false))
           -> ([], env1, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3511 =
             if uvs = []
             then
               let uu____3512 =
                 let uu____3513 = FStar_Syntax_Util.type_u ()  in
                 Prims.fst uu____3513  in
               check_and_gen env2 t uu____3512
             else
               (let uu____3517 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____3517 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3523 =
                        let uu____3524 = FStar_Syntax_Util.type_u ()  in
                        Prims.fst uu____3524  in
                      tc_check_trivial_guard env2 t1 uu____3523  in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2
                       in
                    let uu____3528 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                    (uvs1, uu____3528))
              in
           (match uu____3511 with
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
           let uu____3558 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____3558 with
            | (e1,c,g1) ->
                let uu____3570 =
                  let uu____3574 =
                    let uu____3576 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r
                       in
                    Some uu____3576  in
                  let uu____3577 =
                    let uu____3580 = c.FStar_Syntax_Syntax.lcomp_as_comp ()
                       in
                    (e1, uu____3580)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3574 uu____3577
                   in
                (match uu____3570 with
                 | (e2,uu____3591,g) ->
                     ((let uu____3594 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3594);
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
                 let uu____3636 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____3636
                 then Some q
                 else
                   (let uu____3645 =
                      let uu____3646 =
                        let uu____3649 =
                          let uu____3650 = FStar_Syntax_Print.lid_to_string l
                             in
                          let uu____3651 =
                            FStar_Syntax_Print.quals_to_string q  in
                          let uu____3652 =
                            FStar_Syntax_Print.quals_to_string q'  in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3650 uu____3651 uu____3652
                           in
                        (uu____3649, r)  in
                      FStar_Errors.Error uu____3646  in
                    Prims.raise uu____3645)
              in
           let uu____3655 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3676  ->
                     fun lb  ->
                       match uu____3676 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3700 =
                             let uu____3706 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3706 with
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
                                   | uu____3758 ->
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
                                  (let uu____3766 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef))
                                      in
                                   (false, uu____3766, quals_opt1)))
                              in
                           (match uu____3700 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [], (if quals = [] then None else Some quals)))
              in
           (match uu____3655 with
            | (should_generalize,lbs',quals_opt) ->
                let quals1 =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3820 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___79_3822  ->
                                match uu___79_3822 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3823 -> false))
                         in
                      if uu____3820
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3831 =
                    let uu____3834 =
                      let uu____3835 =
                        let uu____3843 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r
                           in
                        (((Prims.fst lbs), lbs'1), uu____3843)  in
                      FStar_Syntax_Syntax.Tm_let uu____3835  in
                    FStar_Syntax_Syntax.mk uu____3834  in
                  uu____3831 None r  in
                let uu____3865 =
                  let uu____3871 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___99_3875 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___99_3875.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___99_3875.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___99_3875.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___99_3875.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___99_3875.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___99_3875.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___99_3875.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___99_3875.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___99_3875.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___99_3875.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___99_3875.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___99_3875.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___99_3875.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___99_3875.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___99_3875.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___99_3875.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___99_3875.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___99_3875.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___99_3875.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___99_3875.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___99_3875.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___99_3875.FStar_TypeChecker_Env.qname_and_index)
                       }) e
                     in
                  match uu____3871 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3883;
                       FStar_Syntax_Syntax.pos = uu____3884;
                       FStar_Syntax_Syntax.vars = uu____3885;_},uu____3886,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals2 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3905,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals1
                        | uu____3910 -> quals1  in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs1, r, lids, quals2, attrs)), lbs1)
                  | uu____3920 -> failwith "impossible"  in
                (match uu____3865 with
                 | (se1,lbs1) ->
                     ((let uu____3943 = log env2  in
                       if uu____3943
                       then
                         let uu____3944 =
                           let uu____3945 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3952 =
                                         let uu____3957 =
                                           let uu____3958 =
                                             let uu____3963 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____3963.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____3958.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____3957
                                          in
                                       match uu____3952 with
                                       | None  -> true
                                       | uu____3970 -> false  in
                                     if should_log
                                     then
                                       let uu____3975 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____3976 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____3975 uu____3976
                                     else ""))
                              in
                           FStar_All.pipe_right uu____3945
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____3944
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
             (fun uu___80_4006  ->
                match uu___80_4006 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4007 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4015 -> false  in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____4020 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4033,r) ->
          let uu____4041 = is_abstract quals  in
          if uu____4041
          then
            let for_export_bundle se1 uu____4060 =
              match uu____4060 with
              | (out,hidden1) ->
                  (match se1 with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4083,uu____4084,quals1,r1) ->
                       let dec =
                         let uu____4094 =
                           let uu____4101 =
                             FStar_Syntax_Util.maybe_tot_arrow bs t  in
                           (l, us, uu____4101,
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New :: quals1), r1)
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4094  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4108,uu____4109,uu____4110,uu____4111,r1)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r1)
                          in
                       ((dec :: out), (l :: hidden1))
                   | uu____4121 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4133,uu____4134,quals,uu____4136) ->
          let uu____4139 = is_abstract quals  in
          if uu____4139 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4156 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____4156
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____4166 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___81_4168  ->
                       match uu___81_4168 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4171 -> false))
                in
             if uu____4166 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4181 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4193,uu____4194,quals,uu____4196) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____4214 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____4214
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
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4238) ->
          let uu____4245 = is_abstract quals  in
          if uu____4245
          then
            let uu____4250 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu____4256 =
                        let uu____4263 =
                          let uu____4264 =
                            let uu____4269 =
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                               in
                            uu____4269.FStar_Syntax_Syntax.fv_name  in
                          uu____4264.FStar_Syntax_Syntax.v  in
                        (uu____4263, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp),
                          (FStar_Syntax_Syntax.Assumption :: quals), r)
                         in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____4256))
               in
            (uu____4250, hidden)
          else ([se], hidden)
  
let tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4317 se =
        match uu____4317 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4347 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____4347
              then
                let uu____4348 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4348
              else ());
             (let uu____4350 = tc_decl env1 se  in
              match uu____4350 with
              | (ses',env2,ses_elaborated) ->
                  ((let uu____4374 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes"))
                       in
                    if uu____4374
                    then
                      let uu____4375 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4378 =
                                 let uu____4379 =
                                   FStar_Syntax_Print.sigelt_to_string se1
                                    in
                                 Prims.strcat uu____4379 "\n"  in
                               Prims.strcat s uu____4378) "" ses'
                         in
                      FStar_Util.print1 "Checked: %s\n" uu____4375
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4383 =
                      let accum_exports_hidden uu____4401 se1 =
                        match uu____4401 with
                        | (exports1,hidden1) ->
                            let uu____4417 = for_export hidden1 se1  in
                            (match uu____4417 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'
                       in
                    match uu____4383 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated)))))
         in
      let uu____4467 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses  in
      match uu____4467 with
      | (ses1,exports,env1,uu____4493) ->
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
      (let uu____4518 = FStar_Options.debug_any ()  in
       if uu____4518
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
         let uu___100_4524 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___100_4524.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___100_4524.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___100_4524.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___100_4524.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___100_4524.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___100_4524.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___100_4524.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___100_4524.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___100_4524.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___100_4524.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___100_4524.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___100_4524.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___100_4524.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___100_4524.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___100_4524.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___100_4524.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___100_4524.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___100_4524.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___100_4524.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___100_4524.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___100_4524.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___100_4524.FStar_TypeChecker_Env.qname_and_index)
         }  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name
           in
        let uu____4527 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
           in
        match uu____4527 with
        | (ses,exports,env3) ->
            ((let uu___101_4545 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_4545.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___101_4545.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_4545.FStar_Syntax_Syntax.is_interface)
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
        let uu____4561 = tc_decls env decls  in
        match uu____4561 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___102_4579 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___102_4579.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___102_4579.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___102_4579.FStar_Syntax_Syntax.is_interface)
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
          let uu___103_4593 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___103_4593.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___103_4593.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___103_4593.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___103_4593.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___103_4593.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___103_4593.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___103_4593.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___103_4593.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___103_4593.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___103_4593.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___103_4593.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___103_4593.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___103_4593.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___103_4593.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___103_4593.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___103_4593.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___103_4593.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___103_4593.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___103_4593.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___103_4593.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___103_4593.FStar_TypeChecker_Env.qname_and_index)
          }  in
        let check_term lid univs1 t =
          let uu____4604 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____4604 with
          | (univs2,t1) ->
              ((let uu____4610 =
                  let uu____4611 =
                    let uu____4614 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____4614  in
                  FStar_All.pipe_left uu____4611
                    (FStar_Options.Other "Exports")
                   in
                if uu____4610
                then
                  let uu____4615 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____4616 =
                    let uu____4617 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____4617
                      (FStar_String.concat ", ")
                     in
                  let uu____4622 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4615 uu____4616 uu____4622
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____4625 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____4625 Prims.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____4643 =
             let uu____4644 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____4645 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4644 uu____4645
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4643);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt uu___82_4650 =
          match uu___82_4650 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4653,uu____4654)
              ->
              let uu____4661 =
                let uu____4662 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4662  in
              if uu____4661
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4670,uu____4671,uu____4672,r) ->
              let t =
                let uu____4683 =
                  let uu____4686 =
                    let uu____4687 =
                      let uu____4695 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____4695)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____4687  in
                  FStar_Syntax_Syntax.mk uu____4686  in
                uu____4683 None r  in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4707,uu____4708,uu____4709,uu____4710,uu____4711)
              -> check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t,quals,uu____4720)
              ->
              let uu____4723 =
                let uu____4724 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4724  in
              if uu____4723 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4727,lbs),uu____4729,uu____4730,quals,uu____4732) ->
              let uu____4744 =
                let uu____4745 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4745  in
              if uu____4744
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
              let uu____4766 =
                let uu____4767 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4767  in
              if uu____4766
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
          let uu___104_4800 = modul  in
          {
            FStar_Syntax_Syntax.name =
              (uu___104_4800.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___104_4800.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          }  in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
        (let uu____4803 =
           let uu____4804 = FStar_Options.lax ()  in
           Prims.op_Negation uu____4804  in
         if uu____4803 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____4810 =
           let uu____4811 = FStar_Options.interactive ()  in
           Prims.op_Negation uu____4811  in
         if uu____4810
         then
           let uu____4812 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_right uu____4812 Prims.ignore
         else ());
        (modul1, env1)
  
let tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4822 = tc_partial_modul env modul  in
      match uu____4822 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
  
let check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4843 = FStar_Options.debug_any ()  in
       if uu____4843
       then
         let uu____4844 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4844
       else ());
      (let env1 =
         let uu___105_4848 = env  in
         let uu____4849 =
           let uu____4850 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____4850  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___105_4848.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___105_4848.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___105_4848.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___105_4848.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___105_4848.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___105_4848.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___105_4848.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___105_4848.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___105_4848.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___105_4848.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___105_4848.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___105_4848.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___105_4848.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___105_4848.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___105_4848.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___105_4848.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___105_4848.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___105_4848.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4849;
           FStar_TypeChecker_Env.lax_universes =
             (uu___105_4848.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___105_4848.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___105_4848.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___105_4848.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___105_4848.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____4851 = tc_modul env1 m  in
       match uu____4851 with
       | (m1,env2) ->
           ((let uu____4859 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____4859
             then
               let uu____4860 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "%s\n" uu____4860
             else ());
            (let uu____4863 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____4863
             then
               let normalize_toplevel_lets uu___83_4867 =
                 match uu___83_4867 with
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
                       let uu____4894 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____4894 with
                       | (univnames1,e) ->
                           let uu___106_4899 = lb  in
                           let uu____4900 =
                             let uu____4903 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____4903 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___106_4899.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___106_4899.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___106_4899.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___106_4899.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4900
                           }
                        in
                     let uu____4904 =
                       let uu____4913 =
                         let uu____4917 = FStar_List.map update lbs  in
                         (b, uu____4917)  in
                       (uu____4913, r, ids, qs, attrs)  in
                     FStar_Syntax_Syntax.Sig_let uu____4904
                 | se -> se  in
               let normalized_module =
                 let uu___107_4928 = m1  in
                 let uu____4929 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___107_4928.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____4929;
                   FStar_Syntax_Syntax.exports =
                     (uu___107_4928.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___107_4928.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____4930 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____4930
             else ());
            (m1, env2)))
  